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
#include <range/v3/to_container.hpp>
#include <range/v3/view/concat.hpp>
#include <range/v3/view/drop.hpp>

using namespace solidity::yul;

static_assert(SSACFGStackShuffler<BubbleShuffler<SSACFGStackLayoutGenerator::Stack>>, "Bubble shuffler conforms to SSACFGStackShuffler concept.");
static_assert(SSACFGStackShuffler<DanielShuffler<SSACFGStackLayoutGenerator::Stack>>, "Daniel shuffler conforms to SSACFGStackShuffler concept.");

namespace
{

bool constexpr debugOutput = true;

std::vector<SSACFGStackLayoutGenerator::Slot> pileOfJunk(size_t const _size)
{
	return std::vector<SSACFGStackLayoutGenerator::Slot>(_size, SSACFGJunkSlot{});
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
		m_stackLayout[m_cfg.entry].stackIn = Stack(
			m_cfg.arguments |
			ranges::views::reverse |
			ranges::views::transform([](auto&& _variableAndValueId) -> Slot { return std::get<1>(_variableAndValueId); }) |
			ranges::to<std::vector>
		);
		markBlockHasDefinedStackIn(m_cfg.entry);
	}
}

SSACFGStackLayoutGenerator::~SSACFGStackLayoutGenerator() = default;

bool SSACFGStackLayoutGenerator::requiresCleanStack(SSACFG::BlockId const _block) const
{
	auto const notOnRevertPath = !m_junkBlockFinder.blockAllowsAdditionOfJunk(_block);
	return notOnRevertPath;
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
				return SSACFGJunkSlot{};
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
		std::cout << "\tBlock " << _blockId.value << std::boolalpha << " (needs clean stack = " << requiresCleanStack(_blockId) << ")" << '\n';
	yulAssert(!blockIsGenerated(_blockId));
	yulAssert(blockHasDefinedStackIn(_blockId));

	Stack currentStack = m_stackLayout[_blockId].stackIn;
	auto const numOperationsInBlock = m_cfg.block(_blockId).operations.size();
	m_stackLayout[_blockId].operationIn.resize(numOperationsInBlock);
	for (size_t operationIndex = 0; operationIndex < numOperationsInBlock; ++operationIndex)
		currentStack = visitOperation(_blockId, operationIndex, currentStack);
	m_stackLayout[_blockId].stackOut = currentStack;

	markBlockGenerated(_blockId);
	populateBlockSuccessorStackIn(_blockId);
}

SSACFGStackLayoutGenerator::Stack SSACFGStackLayoutGenerator::visitOperation(
	SSACFG::BlockId const _blockId,
	size_t const _operationIndex,
	Stack const& _inputStack
)
{
	yulAssert(_operationIndex < m_cfg.block(_blockId).operations.size());
	auto const& operation = m_cfg.block(_blockId).operations[_operationIndex];
	auto const& operationLiveOut = m_liveness.operationsLiveOut(_blockId)[_operationIndex];

	// literals should have been pulled out a priori and now are treated as push constants
	yulAssert(ranges::none_of(operationLiveOut, IsSSACFGLiteral(m_cfg)));

	auto const liveOutWithoutOutputsSet = operationLiveOut - operation.outputs;
	auto const liveOutWithoutOutputs = std::set<Slot>(liveOutWithoutOutputsSet.begin(), liveOutWithoutOutputsSet.end());
	std::vector<Slot> requiredStackTop;
	if (auto const* call = std::get_if<SSACFG::Call>(&operation.kind))
		if (call->canContinue)
			requiredStackTop.emplace_back(SSACFGFunctionReturnLabel{&call->call.get()});
	requiredStackTop += operation.inputs;

	// todo if we don't require a clean stack, we might as well just bring up the args and leave the rest as-is
	// auto outputStack = BubbleShuffler<Stack>::shuffle(_inputStack, requiredStackTop, liveOutWithoutOutputs);
	// auto stackOut = BubbleShuffler<Stack>::shuffle(_inputStack, requiredStackTop, _inputStack.data);
	auto stack = [&]
	{
		if (requiresCleanStack(_blockId))
			return DanielShuffler<Stack>::shuffle(_inputStack, liveOutWithoutOutputs, requiredStackTop);

		auto const top = std::vector(liveOutWithoutOutputs.begin(), liveOutWithoutOutputs.end()) + requiredStackTop;
		/*size_t nInitialJunk = 0;
		{
			auto it = _inputStack.begin();
			while (it != _inputStack.end() && std::holds_alternative<SSACFGJunkSlot>(*it))
				++it;
			nInitialJunk = static_cast<size_t>(std::distance(_inputStack.begin(), it));
		}
		auto const tail = pileOfJunk(nInitialJunk);*/
		auto const tail = prepareStackTail(_inputStack.stackData(), top, operationLiveOut);
		// auto const tail = pileOfJunk(_inputStack.size());
		// auto const tail = pileOfJunk(_inputStack.numJunkSlots());
		if constexpr(debugOutput)
		{
			std::string operationName = std::visit(util::GenericVisitor(
				[](SSACFG::Call const& _call) { return _call.function.get().name.str(); },
				[](SSACFG::BuiltinCall const& _call) { return _call.builtin.get().name; },
				[](SSACFG::LiteralAssignment const&) -> std::string { return "assign"; }
			), operation.kind);
			std::cout << "\t\t" << operationName << "(" << _inputStack.str(m_cfg) << " -> " << Stack(tail+top).str(m_cfg) << ")\n";
		}
		return DanielShuffler<Stack>::shuffle(
			_inputStack,
			{},
			tail + top
		);
	}();
	m_stackLayout[_blockId].operationIn[_operationIndex] = stack;

	for (size_t i = 0; i < requiredStackTop.size(); ++i)
		stack.pop();
	for (auto const& val: operation.outputs)
		stack.push(val);
		/*if (operationLiveOut.contains(val))
			stack.push(val);
		else
			stack.push(SSACFGJunkSlot{});*/
	return stack;
}

// todo better name here :)
void SSACFGStackLayoutGenerator::populateBlockSuccessorStackIn(SSACFG::BlockId const _blockId)
{
	std::visit(util::GenericVisitor{
		[](SSACFG::BasicBlock::MainExit const&) {},
		[&](SSACFG::BasicBlock::Jump const& _jump)
		{
			populateStackInFromJumpExit(_blockId, _jump);
		},
		[&](SSACFG::BasicBlock::ConditionalJump const& _condJump)
		{
			populateStackInFromConditionalJumpExit(_blockId, _condJump);
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


void SSACFGStackLayoutGenerator::populateStackInFromJumpExit(
	SSACFG::BlockId const _source,
	SSACFG::BasicBlock::Jump const& _jump
)
{
	if (blockHasDefinedStackIn(_jump.target))
		return;

	auto const& targetLiveIn = m_liveness.liveIn(_jump.target);
	yulAssert(ranges::none_of(targetLiveIn, IsSSACFGLiteral(m_cfg)));

	std::set<Slot> const targetLiveInSlots(targetLiveIn.begin(), targetLiveIn.end());
	if (requiresCleanStack(_jump.target))
	{
		// m_stackLayout[_jump.target].stackIn = DanielShuffler<Stack>::shuffle(m_stackLayout[_source].stackOut, targetLiveInSlots, {});
		m_stackLayout[_jump.target].stackIn = BlockStackInShuffler<Stack>::shuffle(m_stackLayout[_source].stackOut, targetLiveInSlots);
		yulAssert(std::set(m_stackLayout[_jump.target].stackIn.begin(), m_stackLayout[_jump.target].stackIn.end()) == targetLiveInSlots);
	}
	else
	{
		// everything in stack out that is not in target live in can be deemed junk
		Stack junkedStackOut(m_stackLayout[_source].stackOut.stackData() |
			ranges::views::transform([&](Slot const& _slot) -> Slot {
				if (std::holds_alternative<SSACFG::ValueId>(_slot) && !targetLiveIn.contains(std::get<SSACFG::ValueId>(_slot)))
					return SSACFGJunkSlot{};
				return _slot;
			}) |
			ranges::to<std::vector>);
		m_stackLayout[_jump.target].stackIn = DanielShuffler<Stack>::shuffle(
			junkedStackOut,
			{},
			pileOfJunk(junkedStackOut.numJunkSlots()) + std::vector(targetLiveInSlots.begin(), targetLiveInSlots.end())
		);

	}
	markBlockHasDefinedStackIn(_jump.target);
}

void SSACFGStackLayoutGenerator::populateStackInFromConditionalJumpExit(
	SSACFG::BlockId const _source,
	SSACFG::BasicBlock::ConditionalJump const& _condJump
)
{
	if (blockHasDefinedStackIn(_condJump.nonZero) && blockHasDefinedStackIn(_condJump.zero))
		return;

	if (!blockHasDefinedStackIn(_condJump.nonZero))
	{
		auto const& zeroLiveIn = m_liveness.liveIn(_condJump.zero);
		yulAssert(ranges::none_of(zeroLiveIn, IsSSACFGLiteral(m_cfg)));
		auto const& nonZeroLiveIn = m_liveness.liveIn(_condJump.nonZero);
		yulAssert(ranges::none_of(nonZeroLiveIn, IsSSACFGLiteral(m_cfg)));

		auto const pulledBackZeroLiveIn = zeroLiveIn | ranges::views::transform(ReversePhiFunctionTransform(m_cfg, _source, _condJump.zero)) | ranges::to<std::set>;

		std::vector<Slot> const nonZeroLiveInSlots(nonZeroLiveIn.begin(), nonZeroLiveIn.end());
		auto const remainingZeroLiveIn = pulledBackZeroLiveIn - nonZeroLiveIn;
		std::vector<Slot> const remainingZeroLiveInSlots(remainingZeroLiveIn.begin(), remainingZeroLiveIn.end());

		// todo use shuffle algo
		if (requiresCleanStack(_condJump.nonZero) && requiresCleanStack(_condJump.zero))
			// [phi^-1(liveInZero) - liveInNonZero, liveInNonZero]
			m_stackLayout[_condJump.nonZero].stackIn = Stack(remainingZeroLiveInSlots + nonZeroLiveInSlots);
		else
		{
			auto const targetLiveIn = remainingZeroLiveIn + nonZeroLiveIn;
			auto const top = remainingZeroLiveInSlots + nonZeroLiveInSlots;
			auto const tail = prepareStackTail(
				m_stackLayout[_source].stackOut.stackData(), // current stack m_stackLayout[_source].stackOut.stackData()
				top + std::vector<Slot>{_condJump.condition}, // we will add the condition, no need if its already there
				targetLiveIn // liveness
			);
			m_stackLayout[_condJump.nonZero].stackIn = Stack(tail + top);
		}

		markBlockHasDefinedStackIn(_condJump.nonZero);
	}

	if (!blockHasDefinedStackIn(_condJump.zero))
	{
		auto const& zeroLiveIn = m_liveness.liveIn(_condJump.zero);
		yulAssert(ranges::none_of(zeroLiveIn, IsSSACFGLiteral(m_cfg)));

		std::vector<Slot> const zeroLiveInStackData(zeroLiveIn.begin(), zeroLiveIn.end());
		// todo use shuffle algo
		if (requiresCleanStack(_condJump.zero))
			m_stackLayout[_condJump.zero].stackIn = Stack(zeroLiveInStackData);
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
			m_stackLayout[_condJump.zero].stackIn = Stack(
				pileOfJunk(m_stackLayout[_source].stackOut.stackData().size()) + zeroLiveInStackData
			);
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
