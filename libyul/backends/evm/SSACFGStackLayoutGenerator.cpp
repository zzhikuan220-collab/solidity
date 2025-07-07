/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0

#include <libyul/backends/evm/SSACFGStackLayoutGenerator.h>

#include <libyul/backends/evm/ControlFlow.h>
#include <libyul/backends/evm/SSACFGBridgeFinder.h>
#include <libyul/backends/evm/SSACFGLiveness.h>
#include <libyul/backends/evm/SSACFGStackShuffler.h>

#include <libsolutil/Visitor.h>

#include <range/v3/algorithm/equal.hpp>
#include <range/v3/algorithm/none_of.hpp>
#include <range/v3/algorithm/remove_if.hpp>
#include <range/v3/algorithm/replace.hpp>
#include <range/v3/view/concat.hpp>
#include <range/v3/view/drop.hpp>
#include <range/v3/view/filter.hpp>
#include <range/v3/view/reverse.hpp>
#include <range/v3/to_container.hpp>

using namespace solidity::yul;
using namespace solidity::yul::ssa;

// todo
// static_assert(SSACFGStackShuffler<BubbleShuffler<SSACFGStackLayoutGenerator::Stack>>, "Bubble shuffler conforms to SSACFGStackShuffler concept.");
static_assert(SSACFGStackShuffler<DanielShuffler<SSACFGStackLayoutGenerator::Stack>>, "Daniel shuffler conforms to SSACFGStackShuffler concept.");

namespace
{

#if !defined(NDEBUG)
bool constexpr debugOutput = true;
#else
bool constexpr debugOutput = false;
#endif

[[maybe_unused]] std::vector<SSACFGStackLayoutGenerator::Slot> pileOfJunk(size_t const _size)
{
	return std::vector<SSACFGStackLayoutGenerator::Slot>(_size, ssa::JunkSlot{});
}


template<typename... TargetTypes, typename... SourceTypes>
std::variant<TargetTypes...> castVariantTypes(std::variant<SourceTypes...> const& v)
{
	return std::visit(
		[]<typename VariantType>(VariantType const& val) -> std::variant<TargetTypes...> {
			if constexpr ((std::is_same_v<VariantType, TargetTypes> || ...)) {
				return val;
			} else {
				yulAssert(false, "Tried casting variant component to invalid type.");
			}
		},
		v
	);
}

template<typename TargetVariant, typename SourceVariant>
TargetVariant castVariant(SourceVariant const& _source) {
	return []<typename... VariantTypes>(std::type_identity<std::variant<VariantTypes...>>, const SourceVariant& _v) {
		return castVariantTypes<VariantTypes...>(_v);
	}(std::type_identity<TargetVariant>{}, _source);
}

}


ControlFlowLayout SSACFGStackLayoutGenerator::generate(ControlFlowLiveness const& _controlFlowLiveness)
{
	ControlFlowLayout layout;
	layout.mainLayout = generate(*_controlFlowLiveness.mainLiveness);

	layout.functionLayouts.reserve(_controlFlowLiveness.functionLiveness.size());
	for (auto const& functionLiveness: _controlFlowLiveness.functionLiveness)
		layout.functionLayouts.push_back(generate(*functionLiveness));

	return layout;
}

SSACFGStackLayout SSACFGStackLayoutGenerator::generate(SSACFGLiveness const& _cfgLiveness)
{
	if constexpr (debugOutput)
		std::cout << "stack layout for " << (_cfgLiveness.cfg().function ? _cfgLiveness.cfg().function->name.str() : "main graph") << '\n';
	return SSACFGStackLayoutGenerator{_cfgLiveness}.run();
}

SSACFGStackLayoutGenerator::SSACFGStackLayoutGenerator(
	SSACFGLiveness const& _liveness
):
	m_liveness(_liveness),
	m_cfg(_liveness.cfg()),
	m_junkBlockFinder(_liveness.cfg(), _liveness.topologicalSort()),
	m_generatedBlocks(_liveness.cfg().numBlocks(), false),
	m_definedStackIn(_liveness.cfg().numBlocks(), false)
{
	m_stackLayout.blockLayouts.resize(m_cfg.numBlocks());
	if (!m_cfg.function)
	{
		// for the main CFG: empty initial stack
		m_stackLayout[m_cfg.entry].stackIn = {};
		markBlockHasDefinedStackIn(m_cfg.entry);
	}
	else
	{
		// for function CFG: arguments are at the top of the stack
		// todo why do i have to copy this explicitly into vector ctor
		m_stackLayout[m_cfg.entry].stackIn = std::vector(
			m_cfg.arguments |
			ranges::views::reverse |
			ranges::views::transform([](auto&& _variableAndValueId) -> ssa::StackSlot { return std::get<1>(_variableAndValueId); }) |
			ranges::to<std::vector>
		);
		markBlockHasDefinedStackIn(m_cfg.entry);
	}
}

SSACFGStackLayoutGenerator::~SSACFGStackLayoutGenerator() = default;

SSACFGStackLayoutGenerator::Stack SSACFGStackLayoutGenerator::layoutToStack(StackData const& _layout) const
{
	Stack::Data stackData;
	stackData.reserve(_layout.size());
	for (auto const& slot: _layout)
		stackData.push_back(castVariant<Stack::Slot>(slot));
	return Stack(std::move(stackData), {}, {&m_cfg});
}

ssa::StackData SSACFGStackLayoutGenerator::stackToLayout(Stack::Data const& _stack, SSACFG::BlockId const& _blockId)
{
	StackData layout;
	layout.reserve(_stack.size());
	for (auto const& slot: _stack)
		if (auto const* phiPreImageSlot = std::get_if<PhiPreImageSlot>(&slot))
		{
			bool foundPhiPreImage = false;
			for (auto const& [phiTargetBlock, phiId]: phiPreImageSlot->phiIds)
				if (phiTargetBlock == _blockId)
				{
					layout.emplace_back(phiId);
					foundPhiPreImage = true;
					break;
				}
			if (!foundPhiPreImage)
				layout.emplace_back(phiPreImageSlot->preImage);
		}
		else
			layout.push_back(castVariant<ssa::StackSlot>(slot));
	return layout;
}

std::vector<SSACFGStackLayoutGenerator::Slot>
SSACFGStackLayoutGenerator::prepareStackTail(
	std::vector<Slot> const& _current,
	std::vector<Slot> const& _newTop,
	std::set<SSACFG::ValueId> const& _liveness
)
{
	auto tail = _current;
	// keep the top elements if they are the same
	{
		for (size_t n = std::min(tail.size(), _newTop.size()); n > 0; --n)
		{
			std::span const topSpan(_newTop.begin(), n);
			std::span const tailSpan(tail.end() - static_cast<std::ptrdiff_t>(n), n);
			if (ranges::equal(topSpan, tailSpan))
			{
				tail = std::vector(tail.begin(), tail.end() - static_cast<std::ptrdiff_t>(n));
				break;
			}
		}
	}
	// junk everything that isn't live-out
	tail = tail |
		ranges::views::transform([&](Slot const& _slot) -> Slot {
			if (std::holds_alternative<SSACFG::ValueId>(_slot) && !_liveness.contains(std::get<SSACFG::ValueId>(_slot)))
				return ssa::JunkSlot{};
			return _slot;
		}) |
		ranges::to<std::vector>;
	return tail;
}

SSACFGStackLayout const& SSACFGStackLayoutGenerator::run()
{
	for (auto const& blockIdValue: m_liveness.topologicalSort().preOrder())
		visitBlock(SSACFG::BlockId{blockIdValue});
	return m_stackLayout;
}

void SSACFGStackLayoutGenerator::visitBlock(SSACFG::BlockId const _blockId)
{
	if constexpr (debugOutput)
		std::cout << "\tBlock " << _blockId.value << std::boolalpha << " (junk can be added = " << m_junkBlockFinder.blockAllowsAdditionOfJunk(_blockId) << ", stackIn=" << stackToString(m_stackLayout[_blockId].stackIn, m_cfg) << ")" << '\n';
	yulAssert(!blockIsGenerated(_blockId));
	yulAssert(blockHasDefinedStackIn(_blockId));

	Stack currentStack = layoutToStack(m_stackLayout[_blockId].stackIn);
	auto const numOperationsInBlock = m_cfg.block(_blockId).operations.size();
	m_stackLayout[_blockId].operationIn.resize(numOperationsInBlock);
	for (size_t operationIndex = 0; operationIndex < numOperationsInBlock; ++operationIndex)
		propagateStackThroughOperation(_blockId, operationIndex, currentStack);
	m_stackLayout[_blockId].stackOut = stackToLayout(currentStack.data(), _blockId);

	markBlockGenerated(_blockId);
	handleBlockSuccessorsStackIn(_blockId);
}

void SSACFGStackLayoutGenerator::propagateStackThroughOperation(
	SSACFG::BlockId const _blockId,
	size_t const _operationIndex,
	Stack& _stack
)
{
	yulAssert(_operationIndex < m_cfg.block(_blockId).operations.size());
	auto const& operation = m_cfg.block(_blockId).operations[_operationIndex];
	auto const& operationLiveOut = m_liveness.operationsLiveOut(_blockId)[_operationIndex];

	if constexpr(debugOutput)
	{
		std::string const operationName = std::visit(util::GenericVisitor(
			[](SSACFG::Call const& _call) { return _call.function.get().name.str(); },
			[](SSACFG::BuiltinCall const& _call) { return _call.builtin.get().name; },
			[](SSACFG::LiteralAssignment const&) -> std::string { return "assign"; }
		), operation.kind);
		std::cout << "\t\t" << operationName << "(" << stackToString(stackToLayout(_stack.data(), _blockId), m_cfg) << " -> ";
	}

	// literals should have been pulled out a priori and now are treated as push constants
	yulAssert(ranges::none_of(operationLiveOut, IsSSACFGLiteral(m_cfg)));

	auto const liveOutWithoutOutputsSet = operationLiveOut - operation.outputs;
	auto const liveOutWithoutOutputs = std::set<Slot>(liveOutWithoutOutputsSet.begin(), liveOutWithoutOutputsSet.end());
	std::vector<Slot> requiredStackTop;
	if (auto const* call = std::get_if<SSACFG::Call>(&operation.kind))
		if (call->canContinue)
			requiredStackTop.emplace_back(ssa::FunctionReturnLabel{&call->call.get()});
	requiredStackTop += operation.inputs;

	auto stack = [&]
	{
		if (!m_junkBlockFinder.blockAllowsAdditionOfJunk(_blockId))
		{
			if constexpr(debugOutput)
				std::cout << "{ " << stackToString(stackToLayout(std::vector(liveOutWithoutOutputs.begin(), liveOutWithoutOutputs.end()), _blockId), m_cfg) << " } + " << stackToString(stackToLayout(requiredStackTop, _blockId), m_cfg) << ")\n";
			if constexpr (false)
			{
				auto inputJunkTailSize = static_cast<std::ptrdiff_t>(junkTailSize(_stack.data()));
				auto inputWithoutJunkTail = Stack({_stack.begin() + inputJunkTailSize, _stack.end()}, {}, {&m_cfg});
				BlockForwardShuffler<Stack>::shuffle(inputWithoutJunkTail, liveOutWithoutOutputs, requiredStackTop);
				inputWithoutJunkTail.addJunkTail(inputJunkTailSize);
				return inputWithoutJunkTail;
			}
			else
				return DanielShuffler<Stack>::shuffle(_stack, liveOutWithoutOutputs, requiredStackTop);
		}

		/*return DanielShuffler<Stack>::shuffle(
			_stack,
			{},
			_stack.data() + requiredStackTop
		);*/

		// todo!!
		if constexpr(debugOutput)
			std::cout << "{ " << stackToString(stackToLayout(pileOfJunk(junkTailSize(_stack.data())), _blockId), m_cfg) << " } + " << stackToString(stackToLayout(requiredStackTop, _blockId), m_cfg) << ")\n";
		auto const v = _stack.data() | ranges::views::transform([&](auto const& _slot) -> Slot { return liveOutWithoutOutputs.contains(_slot) ? _slot : ssa::JunkSlot{}; }) | ranges::to<std::vector<Slot>>;
		return DanielShuffler<Stack>::shuffle(_stack, {}, v + requiredStackTop);
		/*
		// todo this can be done more efficiently by using a sorting algo or similar, at least keeping track of junks in the initial transform
		//		also we generate 2% codebloat by artificially shuffling the junk to the back :-(
		//		OTOH we get stack to deep if not doing it
		auto v = _stack.data() | ranges::views::transform([&](auto const& _slot) -> Slot { return liveOutWithoutOutputs.contains(_slot) ? _slot : ssa::JunkSlot{}; }) | ranges::to<std::vector<Slot>>;
		static auto constexpr isJunk = [](Slot const& _slot) { return std::holds_alternative<ssa::JunkSlot>(_slot); };
		auto const numJunk = ranges::count_if(v, isJunk);
		v = v | ranges::views::filter(std::not_fn(isJunk)) | ranges::to<std::vector<Slot>>;
		v = pileOfJunk(static_cast<std::size_t>(numJunk)) + v;
		*/

		// return Stack(v + requiredStackTop, {}, {&m_cfg});
		// return DanielShuffler<Stack>::shuffle(_stack, {}, pileOfJunk(junkTailSize(_stack.data())) + std::vector(liveOutWithoutOutputs.begin(), liveOutWithoutOutputs.end()) + requiredStackTop);
		// return Stack{_stack.data() + requiredStackTop, {}, {&m_cfg}};
	}();
	m_stackLayout[_blockId].operationIn[_operationIndex] = stackToLayout(stack.data(), _blockId);

	for (size_t i = 0; i < requiredStackTop.size(); ++i)
		stack.pop();
	for (auto const& val: operation.outputs)
		stack.push(val);
	_stack = stack;
}

void SSACFGStackLayoutGenerator::handleBlockSuccessorsStackIn(SSACFG::BlockId const _blockId)
{
	std::visit(util::GenericVisitor{
		[](SSACFG::BasicBlock::MainExit const&) {},
		[&](SSACFG::BasicBlock::Jump const& _jump)
		{
			handleStackInViaJumpExit(_blockId, _jump);
		},
		[&](SSACFG::BasicBlock::ConditionalJump const& _condJump)
		{
			handleStackInViaConditionalJumpExit(_blockId, _condJump);
		},
		[](SSACFG::BasicBlock::JumpTable const&)
		{
			yulAssert(false, "nope, not yet"); // todo
		},
		[](SSACFG::BasicBlock::FunctionReturn const&)
		{
		},
		[](SSACFG::BasicBlock::Terminated const&) {}
	}, m_cfg.block(_blockId).exit);
}

void SSACFGStackLayoutGenerator::handleStackInViaJumpExit(
	SSACFG::BlockId const _source,
	SSACFG::BasicBlock::Jump const& _jump
)
{
	if (blockHasDefinedStackIn(_jump.target))
		return;

	// shortcut for trivial jumps
	if (
		auto const& targetBlock = m_cfg.block(_jump.target);
		targetBlock.entries.size() == 1
	)
	{
		yulAssert(targetBlock.phis.empty());
		m_stackLayout[_jump.target].stackIn = m_stackLayout[_source].stackOut;
		markBlockHasDefinedStackIn(_jump.target);
		return;
	}

	auto const& zeroLiveIn = m_liveness.liveIn(_jump.target);
	auto const pulledBackLiveIn = preImage(zeroLiveIn, _source, _jump.target);

	auto const& sourceStack = layoutToStack(m_stackLayout[_source].stackOut);
	auto numJunk = junkTailSize(sourceStack.data());
	Stack sourceStackWithoutJunkTail({sourceStack.begin() + static_cast<std::ptrdiff_t>(numJunk), sourceStack.end()}, {}, {&m_cfg});
	reduceStackToLiveness(sourceStackWithoutJunkTail, pulledBackLiveIn, m_junkBlockFinder.blockAllowsAdditionOfJunk(_jump.target));

	// add any phi function values here that are not already contained in the stack
	{
		auto stackInData = sourceStackWithoutJunkTail.data();
		ReversePhiFunctionTransform const zeroPreImage(m_cfg, _source, _jump.target);
		handlePhiFunctions(stackInData, zeroPreImage, zeroLiveIn);
		m_stackLayout[_jump.target].stackIn = stackToLayout(pileOfJunk(numJunk) + stackInData, _jump.target);
	}

	markBlockHasDefinedStackIn(_jump.target);
}

void SSACFGStackLayoutGenerator::handleStackInViaConditionalJumpExit(
	SSACFG::BlockId const _source,
	SSACFG::BasicBlock::ConditionalJump const& _condJump
)
{
	// todo i have popped too much. if the variable as well as phi(variable) are requested, they both must end up in the layout!
	//		at the operation level i have forgotten where i came from

	// we can't enter nonZero without `goto`
	yulAssert(!blockHasDefinedStackIn(_condJump.nonZero));
	//if (blockHasDefinedStackIn(_condJump.nonZero) && blockHasDefinedStackIn(_condJump.zero))
	//	return;

	auto const& sourceStack = layoutToStack(m_stackLayout[_source].stackOut);
	auto sourceJunkTailSize = junkTailSize(sourceStack.data());
	std::vector sourceStackWithoutJunkTail(sourceStack.begin() + static_cast<std::ptrdiff_t>(sourceJunkTailSize), sourceStack.end());

	auto const& zeroLiveIn = m_liveness.liveIn(_condJump.zero);
	yulAssert(ranges::none_of(zeroLiveIn, IsSSACFGLiteral(m_cfg)));
	auto const pulledBackZeroLiveIn = preImage(zeroLiveIn, _source, _condJump.zero);
	auto const& nonZeroLiveIn = m_liveness.liveIn(_condJump.nonZero);
	yulAssert(ranges::none_of(nonZeroLiveIn, IsSSACFGLiteral(m_cfg)));
	auto const pulledBackNonZeroLiveIn = preImage(nonZeroLiveIn, _source, _condJump.nonZero);

	Stack conditionalJumpState (sourceStackWithoutJunkTail, {}, {&m_cfg});

	if (!blockHasDefinedStackIn(_condJump.nonZero))
	{
		//auto const pulledBackZeroLiveIn = zeroLiveIn | ranges::views::transform(ReversePhiFunctionTransform(m_cfg, _source, _condJump.zero)) | ranges::to<std::set>;

		//auto const remainingZeroLiveIn = pulledBackZeroLiveIn - nonZeroLiveIn;
		//std::vector<Slot> const remainingZeroLiveInSlots(remainingZeroLiveIn.begin(), remainingZeroLiveIn.end());

		// [phi^-1(liveInZero) - liveInNonZero, liveInNonZero]
		//auto const activeSet = nonZeroLiveIn + remainingZeroLiveIn;

		// this will discard value ids if they overlap in their pre-images. but that is okay here because we don't
		// use any information related to the phi value ids on the combined pre image
		auto const combinedPreImage = pulledBackNonZeroLiveIn + pulledBackZeroLiveIn;

		// pop everything not in the combined pre image
		// we can ignore the phi function pre-image slots because they are definitely in the combined liveness
		reduceStackToLiveness(conditionalJumpState, combinedPreImage, false);

		// add any phi function values here that are not already contained in the stack
		{
			auto stackInData = conditionalJumpState.data();
			ReversePhiFunctionTransform nonZeroPreImage(m_cfg, _source, _condJump.nonZero);
			handlePhiFunctions(stackInData, nonZeroPreImage, nonZeroLiveIn);
			m_stackLayout[_condJump.nonZero].stackIn = stackToLayout(pileOfJunk(sourceJunkTailSize) + stackInData, _condJump.nonZero);
		}

		markBlockHasDefinedStackIn(_condJump.nonZero);
	}

	if (!blockHasDefinedStackIn(_condJump.zero))
	{
		reduceStackToLiveness(conditionalJumpState, pulledBackZeroLiveIn, m_junkBlockFinder.blockAllowsAdditionOfJunk(_condJump.zero));

		// add any phi function values here that are not already contained in the stack
		{
			auto stackInData = conditionalJumpState.data();
			ReversePhiFunctionTransform zeroPreImage(m_cfg, _source, _condJump.zero);
			handlePhiFunctions(stackInData, zeroPreImage, zeroLiveIn);
			m_stackLayout[_condJump.zero].stackIn = stackToLayout(pileOfJunk(sourceJunkTailSize) + stackInData, _condJump.zero);
		}
		markBlockHasDefinedStackIn(_condJump.zero);
	}
}

bool SSACFGStackLayoutGenerator::blockIsGenerated(SSACFG::BlockId const _blockId) const
{
	return m_generatedBlocks[_blockId.value];
}

void SSACFGStackLayoutGenerator::markBlockGenerated(SSACFG::BlockId const _blockId)
{
	m_generatedBlocks[_blockId.value] = true;
}

bool SSACFGStackLayoutGenerator::blockHasDefinedStackIn(SSACFG::BlockId const _blockId) const
{
	return m_definedStackIn[_blockId.value];
}

void SSACFGStackLayoutGenerator::markBlockHasDefinedStackIn(SSACFG::BlockId const _blockId)
{
	m_definedStackIn[_blockId.value] = true;
}
size_t SSACFGStackLayoutGenerator::junkTailSize(std::vector<Stack::Slot> const& _stack)
{
	std::size_t numJunk = 0;
	auto it = _stack.begin();
	while (it != _stack.end() && std::holds_alternative<ssa::JunkSlot>(*it))
	{
		++numJunk;
		++it;
	}
	return numJunk;
}

std::set<SSACFG::ValueId> SSACFGStackLayoutGenerator::preImage(
	std::set<SSACFG::ValueId> const& _valueIds,
	SSACFG::BlockId const& _from,
	SSACFG::BlockId const& _to
) const
{
	return _valueIds | ranges::views::transform(ReversePhiFunctionTransform(m_cfg, _from, _to)) | ranges::to<std::set>;
}

SSACFGStackLayoutGenerator::Stack SSACFGStackLayoutGenerator::shuffleStack(
	Stack const& _source, std::vector<Slot> _target, std::optional<SSACFG::Edge> const& _edge) const
{
	auto const transform
		= _edge ? ReversePhiFunctionTransform(m_cfg, _edge->from, _edge->to) : ReversePhiFunctionTransform{};
	auto const transformedTarget = [&]
	{
		if (transform.noOp())
			return _target;
		return _target | ranges::views::transform(transform) | ranges::to<std::vector>;
	}();
	auto result = DanielShuffler<Stack>::shuffle(_source, {}, transformedTarget);
	// todo check if stack too deep, try compressing stack by getting rid of junk
	// todo if can't get rid of junk to fix the situation, move to memory
	return Stack(_target, {}, {&m_cfg});
}

void SSACFGStackLayoutGenerator::reduceStackToLiveness(Stack& _stack, std::set<SSACFG::ValueId> const& _livenessPreImage, bool _introduceJunk)
{
	// pop everything not in the combined pre image
	// we can ignore the phi function pre-image slots because they are definitely in the combined liveness
	while (
		_stack.size() > 0 &&
		std::holds_alternative<SSACFG::ValueId>(_stack.top()) &&
		!_livenessPreImage.contains(std::get<SSACFG::ValueId>(_stack.top()))
	)
		_stack.pop();
	for (auto it = _stack.data().rbegin(); it != _stack.data().rend(); ++it)
	{
		if (std::holds_alternative<SSACFG::ValueId>(*it) && !_livenessPreImage.contains(std::get<SSACFG::ValueId>(*it)))
		{
			yulAssert(
				it != _stack.data().rbegin()); // this shouldn't happen as we have already popped everything up front
			auto const depth = static_cast<std::size_t>(std::distance(_stack.data().rbegin(), it));
			if (_introduceJunk)
				_stack.declareJunk(depth);
			else
			{
				if (depth > 0)
					_stack.swap(depth);
				_stack.pop();
			}
		}
	}
}

void SSACFGStackLayoutGenerator::handlePhiFunctions(
	Stack::Data& _stackData,
	ReversePhiFunctionTransform const& _phiInverse,
	std::set<SSACFG::ValueId> const& _liveness
)
{
	// add any phi function values here that are not already contained in the stack
	for (auto const& [phi, preImage]: _phiInverse.data())
	{
		// yulAssert(nonZeroLiveIn.contains(phi));
		// v = phi^{-1}(v_phi)
		// auto const& preImage = nonZeroPreImage.data().at(phi);
		auto it = ranges::find(_stackData, Slot{preImage});
		if (_liveness.contains(preImage))
		{
			// both the phi function and the pre image are part of the live in set
			// we check if there is more than one v
			// if so, one of them is symbolically replaced by the phi function
			// otherwise, we push the phi function value
			// we must have the pre image here at least once, otherwise it's an invalid dup
			yulAssert(it != _stackData.end());
			auto it2 = ranges::find(it + 1, _stackData.end(), Slot{preImage});
			if(it2 != _stackData.end())
				*it2 = phi;
			else
				_stackData.emplace_back(phi);
		}
		else
		{
			// replace all v with phi
			ranges::replace(_stackData, Slot{preImage}, Slot{phi});
			// if its not contained, push it
			if (it == _stackData.end())
				_stackData.emplace_back(phi);
		}
	}
}
