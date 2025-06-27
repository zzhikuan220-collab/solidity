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

#include <range/v3/algorithm/none_of.hpp>
#include <range/v3/view/reverse.hpp>

#include <range/v3/algorithm/equal.hpp>
#include <range/v3/algorithm/remove_if.hpp>
#include <range/v3/view/concat.hpp>
#include <range/v3/view/drop.hpp>
#include <range/v3/view/filter.hpp>
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

ssa::StackData SSACFGStackLayoutGenerator::stackToLayout(Stack::Data const& _stack)
{
	StackData layout;
	layout.reserve(_stack.size());
	for (auto const& slot: _stack)
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
	m_stackLayout[_blockId].stackOut = stackToLayout(currentStack.data());

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
		std::cout << "\t\t" << operationName << "(" << stackToString(stackToLayout(_stack.data()), m_cfg) << " -> ";
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
				std::cout << "{ " << stackToString(stackToLayout(std::vector(liveOutWithoutOutputs.begin(), liveOutWithoutOutputs.end())), m_cfg) << " } + " << stackToString(stackToLayout(requiredStackTop), m_cfg) << ")\n";
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
			std::cout << "{ " << stackToString(stackToLayout(pileOfJunk(junkTailSize(_stack.data()))), m_cfg) << " } + " << stackToString(stackToLayout(requiredStackTop), m_cfg) << ")\n";
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
	m_stackLayout[_blockId].operationIn[_operationIndex] = stackToLayout(stack.data());

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

	auto const& targetLiveIn = m_liveness.liveIn(_jump.target);
	yulAssert(ranges::none_of(targetLiveIn, IsSSACFGLiteral(m_cfg)));

	auto const& sourceStack = layoutToStack(m_stackLayout[_source].stackOut);
	auto numJunk = static_cast<std::ptrdiff_t>(junkTailSize(sourceStack.data()));
	Stack const sourceStackWithoutJunkTail = Stack({sourceStack.begin() + numJunk, sourceStack.end()}, {}, {&m_cfg});
	std::set<Slot> const targetLiveInSlots(targetLiveIn.begin(), targetLiveIn.end());

	//auto const& targetUsed = m_liveness.used(_jump.target);
	//auto const targetUnused = targetLiveIn - targetUsed;
	//std::set<Slot> const targetLiveInUnusedSlots(targetUnused.begin(), targetUnused.end());
	//std::vector<Slot> targetUsedSlots(targetUsed.begin(), targetUsed.end());


	if (!m_junkBlockFinder.blockAllowsAdditionOfJunk(_jump.target))
	{
		/*m_stackLayout[_jump.target].stackIn = shuffleStack(
			Stack(sourceStackData, {}, {&m_cfg}),
			std::vector(targetLiveInSlots.begin(), targetLiveInSlots.end()),
			SSACFG::Edge{_source, _jump.target}
		).data();*/
		auto const stackIn = BlockStackInShuffler<Stack>::shuffle(sourceStack, targetLiveInSlots);
		m_stackLayout[_jump.target].stackIn = stackToLayout(stackIn.data());
		// todo fix slot types
		// yulAssert(std::set(m_stackLayout[_jump.target].stackIn.begin(), m_stackLayout[_jump.target].stackIn.end()) == targetLiveInSlots);
	}
	else
	{
		m_stackLayout[_jump.target].stackIn = stackToLayout(pileOfJunk(junkTailSize(sourceStack.data())) + std::vector(targetLiveInSlots.begin(), targetLiveInSlots.end()));
		// m_stackLayout[_jump.target].stackIn = shuffleStack(Stack(sourceStackData, {}, {&m_cfg}), sourceStackData + std::vector(targetLiveInSlots.begin(), targetLiveInSlots.end()), SSACFG::Edge{_source, _jump.target}).data();
	}
	markBlockHasDefinedStackIn(_jump.target);
}

void SSACFGStackLayoutGenerator::handleStackInViaConditionalJumpExit(
	SSACFG::BlockId const _source,
	SSACFG::BasicBlock::ConditionalJump const& _condJump
)
{
	if (blockHasDefinedStackIn(_condJump.nonZero) && blockHasDefinedStackIn(_condJump.zero))
		return;

	auto const& sourceStack = layoutToStack(m_stackLayout[_source].stackOut);
	auto sourceJunkTailSize = junkTailSize(sourceStack.data());
	std::vector const sourceStackWithoutJunkTail(sourceStack.begin() + static_cast<std::ptrdiff_t>(sourceJunkTailSize), sourceStack.end());
	Stack conditionalJumpState (sourceStackWithoutJunkTail, {}, {&m_cfg});

	auto const& zeroLiveIn = m_liveness.liveIn(_condJump.zero);
	yulAssert(ranges::none_of(zeroLiveIn, IsSSACFGLiteral(m_cfg)));
	auto const zeroPreImage = preImage(zeroLiveIn, _source, _condJump.zero);
	if (!blockHasDefinedStackIn(_condJump.nonZero))
	{
		yulAssert(ranges::none_of(zeroLiveIn, IsSSACFGLiteral(m_cfg)));
		auto const& nonZeroLiveIn = m_liveness.liveIn(_condJump.nonZero);
		yulAssert(ranges::none_of(nonZeroLiveIn, IsSSACFGLiteral(m_cfg)));

		auto const nonZeroPreImage = preImage(nonZeroLiveIn, _source, _condJump.nonZero);

		auto combinedPreImage = nonZeroPreImage;
		for (auto const& preImageId: zeroPreImage)
		{
			auto it = combinedPreImage.find(preImageId);
			if (it != combinedPreImage.end() && !it->phiIds.empty())
			{
				yulAssert(!preImageId.phiIds.empty());
				auto nodeHandle = combinedPreImage.extract(it);
				nodeHandle.value().phiIds += preImageId.phiIds;
				combinedPreImage.insert(std::move(nodeHandle));
			}
			else
				combinedPreImage.insert(preImageId);
		}

		//auto const pulledBackZeroLiveIn = zeroLiveIn | ranges::views::transform(ReversePhiFunctionTransform(m_cfg, _source, _condJump.zero)) | ranges::to<std::set>;

		//auto const remainingZeroLiveIn = pulledBackZeroLiveIn - nonZeroLiveIn;
		//std::vector<Slot> const remainingZeroLiveInSlots(remainingZeroLiveIn.begin(), remainingZeroLiveIn.end());

		// [phi^-1(liveInZero) - liveInNonZero, liveInNonZero]
		//auto const activeSet = nonZeroLiveIn + remainingZeroLiveIn;

		if (!m_junkBlockFinder.blockAllowsAdditionOfJunk(_condJump.nonZero) && !m_junkBlockFinder.blockAllowsAdditionOfJunk(_condJump.zero))
		{
			// pop everything not in the active set
			while (
				conditionalJumpState.size() > 0 &&
				std::holds_alternative<SSACFG::ValueId>(conditionalJumpState.top()) &&
				!combinedPreImage.contains(PreImageValueId{{}, std::get<SSACFG::ValueId>(conditionalJumpState.top())})
			)
				conditionalJumpState.pop();
			for (auto it = conditionalJumpState.data().rbegin(); it != conditionalJumpState.data().rend(); ++it)
			{
				if (std::holds_alternative<SSACFG::ValueId>(*it) && !combinedPreImage.contains(PreImageValueId{{}, std::get<SSACFG::ValueId>(*it)}))
				{
					yulAssert(it != conditionalJumpState.data().rbegin()); // this shouldn't happen as we have already popped everything up front
					auto const depth = static_cast<std::size_t>(std::distance(conditionalJumpState.data().rbegin(), it));
					if (depth > 0)
						conditionalJumpState.swap(depth);
					conditionalJumpState.pop();
				}
			}

			m_stackLayout[_condJump.nonZero].stackIn = stackToLayout(pileOfJunk(sourceJunkTailSize) + conditionalJumpState.data());
		}
		else
		{
			while (
				conditionalJumpState.size() > 0 &&
				std::holds_alternative<SSACFG::ValueId>(conditionalJumpState.top()) &&
				!combinedPreImage.contains(PreImageValueId{{}, std::get<SSACFG::ValueId>(conditionalJumpState.top())})
			)
				conditionalJumpState.pop();

			for (auto it = conditionalJumpState.data().rbegin(); it != conditionalJumpState.data().rend(); ++it)
				if (std::holds_alternative<SSACFG::ValueId>(*it) && !combinedPreImage.contains(PreImageValueId{{}, std::get<SSACFG::ValueId>(*it)}))
				{
					yulAssert(it != conditionalJumpState.data().rbegin()); // this shouldn't happen as we have already popped everything up frong
					auto const depth = static_cast<std::size_t>(std::distance(conditionalJumpState.data().rbegin(), it));
					conditionalJumpState.declareJunk(depth);
				}

			m_stackLayout[_condJump.nonZero].stackIn = stackToLayout(pileOfJunk(sourceJunkTailSize) + conditionalJumpState.data());
		}
		markBlockHasDefinedStackIn(_condJump.nonZero);
	}

	if (!blockHasDefinedStackIn(_condJump.zero))
	{
		// pop everything not in the active set
		while (
			conditionalJumpState.size() > 0 &&
			std::holds_alternative<SSACFG::ValueId>(conditionalJumpState.top()) &&
			!zeroPreImage.contains(PreImageValueId{{}, std::get<SSACFG::ValueId>(conditionalJumpState.top())})
		)
			conditionalJumpState.pop();
		for (auto it = conditionalJumpState.data().rbegin(); it != conditionalJumpState.data().rend(); ++it)
		{
			if (std::holds_alternative<SSACFG::ValueId>(*it) && !zeroPreImage.contains(PreImageValueId{{}, std::get<SSACFG::ValueId>(*it)}))
			{
				yulAssert(it != conditionalJumpState.data().rbegin()); // this shouldn't happen as we have already popped everything up front
				auto const depth = static_cast<std::size_t>(std::distance(conditionalJumpState.data().rbegin(), it));
				if (depth > 0)
					conditionalJumpState.swap(depth);
				conditionalJumpState.pop();
			}
		}
		if (!m_junkBlockFinder.blockAllowsAdditionOfJunk(_condJump.zero))
			m_stackLayout[_condJump.zero].stackIn = stackToLayout(std::vector<Slot>(zeroLiveIn.begin(), zeroLiveIn.end()));
		else
			m_stackLayout[_condJump.zero].stackIn = stackToLayout(pileOfJunk(junkTailSize(conditionalJumpState.data())) + std::vector<Slot>(zeroLiveIn.begin(), zeroLiveIn.end()));
		if (!m_junkBlockFinder.blockAllowsAdditionOfJunk(_condJump.zero))
		{
			/*m_stackLayout[_condJump.zero].stackIn =
				std::vector<Slot>(static_cast<size_t>(sourceJunkTailSize), ssa::JunkSlot{}) +
				zeroUnusedLiveInStackData +
				zeroUsedSlots;*/
		}
		else
		{
			/*Stack remainder(m_stackLayout[_source].stackOut.stackData() |
				ranges::views::transform([&](Slot const& _slot) -> Slot {
					if (std::holds_alternative<SSACFG::ValueId>(_slot) && !zeroLiveIn.contains(std::get<SSACFG::ValueId>(_slot)))
						return SSACFGJunkSlot{};
					return _slot;
				}) |
				ranges::to<std::vector>);
			auto const tail = prepareStackTail(
				m_stackLayout[_source].stackOut.stackData(), // current stack
				zeroLiveInStackData,
				zeroLiveIn
			);*/
			/*m_stackLayout[_condJump.zero].stackIn =
				pileOfJunk(m_stackLayout[_source].stackOut.size()) +
				zeroUnusedLiveInStackData +
				zeroUsedSlots;*/
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

std::set<SSACFGStackLayoutGenerator::PreImageValueId> SSACFGStackLayoutGenerator::preImage(
	std::set<SSACFG::ValueId> const& _valueIds,
	SSACFG::BlockId const& _from,
	SSACFG::BlockId const& _to
) const
{
	std::set<PreImageValueId> result;
	auto const transform = ReversePhiFunctionTransform(m_cfg, _from, _to);

	for (auto const& valueId: _valueIds)
	{
		auto const it = transform.data().find(valueId);
		if (it == transform.data().end())
			result.insert(PreImageValueId{{}, valueId});
		else
			result.insert(PreImageValueId{{{_to, valueId}}, it->second});
	}

	return result;
}

SSACFGStackLayoutGenerator::Stack SSACFGStackLayoutGenerator::shuffleStack(Stack const& _source, std::vector<Slot> _target, std::optional<SSACFG::Edge> const& _edge) const
{
	auto const transform = _edge ? ReversePhiFunctionTransform(m_cfg, _edge->from, _edge->to) : ReversePhiFunctionTransform{};
	auto const transformedTarget = [&]
	{
		if (transform.noOp())
			return _target;
		return _target | ranges::views::transform(transform) | ranges::to<std::vector>;
	}();
	auto result = DanielShuffler<Stack>::shuffle(
		_source,
		{}, transformedTarget
	);
	// assertLayoutCompatibility(m_stack.data(), transformedTarget);
	return Stack(_target, {}, {&m_cfg});
}
