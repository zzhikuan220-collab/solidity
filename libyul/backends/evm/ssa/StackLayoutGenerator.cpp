#include "libyul/backends/evm/SSACFGLiveness.h"
#include "libyul/backends/evm/SSACFGStackShuffler.h"
#include "range/v3/algorithm/none_of.hpp"
#include "range/v3/algorithm/replace.hpp"
#include "range/v3/algorithm/sort.hpp"


#include <libyul/backends/evm/ssa/StackLayoutGenerator.h>
#include <queue>
#include <ranges>

using namespace solidity::yul;
using namespace solidity::yul::ssa;

namespace
{
#if !defined(NDEBUG)
bool constexpr debugOutput = true;
#else
bool constexpr debugOutput = false;
#endif
template<typename Slot>
[[maybe_unused]] std::vector<Slot> pileOfJunk(size_t const _size)
{
	return std::vector<Slot>(_size, ssa::JunkSlot{});
}

/*class IsSSACFGLiteral
{
public:
	explicit IsSSACFGLiteral(SSACFG const& _cfg): m_cfg(_cfg) {}

	bool operator()(SSACFG::ValueId const _valueId) const { return m_cfg.isLiteralValue(_valueId); }
	bool operator()(SSACFGStackLayout::Slot const& _slot) const
	{
		return std::holds_alternative<SSACFG::ValueId>(_slot) && (*this)(std::get<SSACFG::ValueId>(_slot));
	}

private:
	SSACFG const& m_cfg;
};*/

void declareJunk(StackLayoutGenerator::StackType& _stack, SSACFGLiveness::LivenessData const& _live)
{
	for (size_t depth = 0; depth < _stack.size(); ++depth)
		if (auto const* valueId = std::get_if<SSACFG::ValueId>(&_stack.slot(depth)))
			if (!_live.contains(*valueId))
				_stack.declareJunk(depth);
}

void junkShuffler(StackLayoutGenerator::StackType& _stack)
{
	// goal is to have the junk in one block at the bottom
	auto numJunk = ranges::count_if(_stack, [](auto const& _slot) { return std::holds_alternative<ssa::JunkSlot>(_slot); });
	size_t i = 0;
	while (numJunk > 0 && i < numJunk)
	{
		auto const depth = _stack.size() - i - 1;
		if (std::holds_alternative<ssa::JunkSlot>(_stack.data()[i]))
		{
			// we have a block of i junk slots at the bottom
			++i;
			continue;
		}

		if (std::holds_alternative<ssa::JunkSlot>(_stack.top()))
		{
			// todo it might be cheaper to swap or to pop
			/*// if we can reach the non-junk slot, swap it up, else pop the junk
			if (depth <= 16)
			{
				_stack.swap(depth);
				++i;
				continue;
			}
			else*/
			{
				_stack.pop();
				--numJunk;
				continue;
			}
		}

		// find the next best junk to swap to the top:
		//   - if there is a junk slot in reach that is in isolation, ie, surrounded by non-junk, take that one
		//   - otherwise, if just take whatever junk slot is in reach
		//   - if none is in reach, give up and break
		std::optional<size_t> nonIsolatedJunk(std::nullopt);
		std::optional<size_t> isolatedJunk(std::nullopt);
		for (size_t junkDepth = 1; junkDepth < std::min(static_cast<size_t>(17), _stack.size()); ++junkDepth)
			if (std::holds_alternative<ssa::JunkSlot>(_stack.slot(junkDepth)))
			{
				bool isolated = !std::holds_alternative<ssa::JunkSlot>(_stack.slot(junkDepth - 1));
				if (junkDepth + 1 < _stack.size())
					isolated &= !std::holds_alternative<ssa::JunkSlot>(_stack.slot(junkDepth + 1));

				if (isolated)
				{
					isolatedJunk = junkDepth;
					break;
				}

				if (!nonIsolatedJunk)
					nonIsolatedJunk = junkDepth;
			}

		if (isolatedJunk)
		{
			_stack.swap(*isolatedJunk);
			continue;
		}

		if (nonIsolatedJunk)
		{
			_stack.swap(*nonIsolatedJunk);
			continue;
		}

		break;
	}
}

}

StackLayoutGenerator::StackLayoutGenerator(SSACFGLiveness const& _liveness):
	m_liveness(_liveness),
	m_cfg(_liveness.cfg()),
	m_blockIsGenerated(m_cfg.numBlocks(), false),
	m_blockHasStackInDefined(m_cfg.numBlocks(), false),
	m_junkBlockFinder(_liveness.cfg(), _liveness.topologicalSort())
{
	m_stackLayout.blockLayouts.resize(m_cfg.numBlocks());
}

ControlFlowLayout StackLayoutGenerator::generate(ControlFlowLiveness const& _controlFlowLiveness)
{
	ControlFlowLayout layout;
	layout.mainLayout = generate(*_controlFlowLiveness.mainLiveness);

	layout.functionLayouts.reserve(_controlFlowLiveness.functionLiveness.size());
	for (auto const& functionLiveness: _controlFlowLiveness.functionLiveness)
		layout.functionLayouts.push_back(generate(*functionLiveness));

	return layout;
}

SSACFGStackLayout StackLayoutGenerator::generate(SSACFGLiveness const& _cfgLiveness)
{
	if constexpr (debugOutput)
		std::cout << "stack layout for "
				  << (_cfgLiveness.cfg().function ? _cfgLiveness.cfg().function->name.str() : "main graph") << '\n';
	return StackLayoutGenerator{_cfgLiveness}.computeStackLayout();
}
void StackLayoutGenerator::handlePhiFunctions(StackData& _stackData, ReversePhiFunctionTransform const& _phiInverse, SSACFGLiveness::LivenessData const& _liveness)
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
			// Both the phi function and the pre image are part of the live in set.
			// We check if there is more than one v.
			// If so, one of them is symbolically replaced by the phi function;
			// otherwise, we push the phi function value.
			// We must have the pre image here at least once, otherwise it's an invalid dup
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
			// if its not contained, push it (could be derived from a literal)
			if (it == _stackData.end())
				_stackData.emplace_back(phi);
		}
	}
}

SSACFGStackLayout const& StackLayoutGenerator::computeStackLayout()
{
	// traverse the cfg layer-wise using Kahn's algorithm
	// like this, (most of) the entry exit layouts are known when a block is processed

	std::vector<std::size_t> inDegreesIgnoringBackedges(m_cfg.numBlocks(), 0);

	for (SSACFG::BlockId id{0}; id.value < m_cfg.numBlocks(); ++id.value)
		for (auto const& entry: m_cfg.block(id).entries)
			if (!m_liveness.topologicalSort().backEdge(entry, id))
				inDegreesIgnoringBackedges[id.value] += 1;

	std::queue<SSACFG::BlockId> traversalQueue;
	traversalQueue.push(m_cfg.entry);

	size_t numVisited = 0;
	while (!traversalQueue.empty())
	{
		auto currentBlockId = traversalQueue.front();
		traversalQueue.pop();

		visitBlock(currentBlockId);

		m_cfg.block(currentBlockId).forEachExit([&](SSACFG::BlockId const& _exit){
			if (--inDegreesIgnoringBackedges[_exit.value] == 0)
				traversalQueue.push(_exit);
		});
		++numVisited;
	}
	yulAssert(numVisited == m_liveness.topologicalSort().preOrder().size());

	// todo unnecessary copy here
	return m_stackLayout;
}

void StackLayoutGenerator::defineStackIn(SSACFG::BlockId const& _blockId)
{
	if (_blockId == m_cfg.entry)
	{
		if (!m_cfg.function)
			m_stackLayout[m_cfg.entry].stackIn = {};
		else
			m_stackLayout[m_cfg.entry].stackIn =
				m_cfg.arguments |
				ranges::views::reverse |
				ranges::views::transform([](auto&& _variableAndValueId) -> Slot { return std::get<1>(_variableAndValueId); }) |
				ranges::to<std::vector>;
		m_blockHasStackInDefined[_blockId.value] = true;
		return;
	}

	auto const& block = m_cfg.block(_blockId);

	std::vector<std::pair<SSACFG::BlockId, StackData const*>> parentExits;
	for (auto const& entry: block.entries)
		if (m_blockIsGenerated[entry.value])
			parentExits.emplace_back(entry, &m_stackLayout[entry].stackOut);

	yulAssert(!parentExits.empty(), fmt::format("None of the parents of block {} were generated", _blockId));

	if (block.entries.size() == 1)
	{
		// pass through
		yulAssert(block.phis.empty());
		yulAssert(parentExits.size() == 1);
		// todo option1: shuffle junk to the bottom and/or pop it if non-junk isn't reachable
		// todo option2: pass through
		// todo option3: hard sort by usage frequency
		m_stackLayout[_blockId].stackIn = *parentExits[0].second;

		/*StackType stackIn(m_stackLayout[_blockId].stackIn, {}, {&m_cfg});
		declareJunk(stackIn, liveIn);

		auto numJunk = ranges::count_if(stackIn, [](auto const& _slot) { return std::holds_alternative<ssa::JunkSlot>(_slot); });
		// junkShuffler(stackIn);
		m_stackLayout[_blockId].stackIn = pileOfJunk<Slot>(numJunk);
		{
			std::vector sortedLiveIn(liveIn.begin(), liveIn.end());
			ranges::sort(sortedLiveIn, [](auto const& l1, auto const& l2) { return std::get<1>(l1) > std::get<1>(l2); });
			for (const auto& var: sortedLiveIn | ranges::views::keys)
				if (!block.phis.contains(var) && !usedVariables.contains(var))
					unifiedStack.emplace_back(var);
		}*/
	}
	else
	{
		// we have more than one entry and need to unify or at the very least apply phi fct.
		auto const& liveIn = m_liveness.liveIn(_blockId);
		/*auto usedVariables = m_liveness.used(_blockId);

		// todo use the most fitting one
		//		from grey approach and each of the predecessor stacks
		// phis at the top
		std::vector<Slot> unifiedStack(block.phis.begin(), block.phis.end());
		// then all variables that are used
		// todo could be sorted by usage frequency
		{
			std::vector sortedUsedVars(usedVariables.begin(), usedVariables.end());
			ranges::sort(sortedUsedVars, [](auto const& l1, auto const& l2) { return std::get<1>(l1) > std::get<1>(l2); });
			for (const auto& var: sortedUsedVars | ranges::views::keys)
				if (!block.phis.contains(var))
					unifiedStack.emplace_back(var);
		}
		// then all variables that are live in but not used
		{
			std::vector sortedLiveIn(liveIn.begin(), liveIn.end());
			ranges::sort(sortedLiveIn, [](auto const& l1, auto const& l2) { return std::get<1>(l1) > std::get<1>(l2); });
			for (const auto& var: sortedLiveIn | ranges::views::keys)
				if (!block.phis.contains(var) && !usedVariables.contains(var))
					unifiedStack.emplace_back(var);
		}*/

		// todo junk

		/*StackData unifiedStack;
		for (auto targetVar : targetStackLayout) {
			// Case 1: Phi function mapping
			if (auto phiInput = getPhiMapping(targetVar, predecessorId)) {
				unifiedStack.push_back(*phiInput);
			}
			// Case 2: Direct variable (if live in this predecessor)
			else if (isLiveInPredecessor(targetVar, predecessorId)) {
				unifiedStack.push_back(targetVar);
			}
			// Case 3: Skip! (no "bottom" needed)
		}*/
		m_stackLayout[_blockId].stackIn = *parentExits[0].second;
		StackType stack(m_stackLayout[_blockId].stackIn, {}, {&m_cfg});
		declareJunk(stack, liveIn);
		handlePhiFunctions(m_stackLayout[_blockId].stackIn, ReversePhiFunctionTransform(m_cfg, parentExits[0].first, _blockId), liveIn);
		//m_stackLayout[_blockId].stackIn = unifiedStack | ranges::views::reverse | ranges::to<std::vector>;
	}

	m_blockHasStackInDefined[_blockId.value] = true;
}

void StackLayoutGenerator::visitBlock(SSACFG::BlockId const& _blockId)
{
	yulAssert(!m_blockIsGenerated[_blockId.value]);
	defineStackIn(_blockId);
	yulAssert(m_blockHasStackInDefined[_blockId.value]);

	StackData currentStackData = m_stackLayout[_blockId].stackIn;
	StackType stack(currentStackData, {}, {&m_cfg});
	bool const junkCanBeAdded = m_junkBlockFinder.blockAllowsAdditionOfJunk(_blockId);
	if constexpr (debugOutput)
		std::cout << fmt::format(
			"\tBlock {} (junk={}, stackIn={})\n", _blockId, junkCanBeAdded, stackToString(currentStackData, m_cfg));

	SSACFG::BasicBlock const& block = m_cfg.block(_blockId);

	auto const& operationsLiveOut = m_liveness.operationsLiveOut(_blockId);
	m_stackLayout[_blockId].operationIn.reserve(block.operations.size());
	for (size_t operationIndex = 0; operationIndex < block.operations.size(); ++operationIndex)
	{
		SSACFG::Operation const& operation = block.operations[operationIndex];
		SSACFGLiveness::LivenessData opLiveOut = operationsLiveOut[operationIndex];

		if constexpr(debugOutput)
		{
			std::string const operationName = std::visit(util::GenericVisitor(
				[](SSACFG::Call const& _call) { return _call.function.get().name.str(); },
				[](SSACFG::BuiltinCall const& _call) { return _call.builtin.get().name; },
				[](SSACFG::LiteralAssignment const&) -> std::string { return "assign"; }
			), operation.kind);
			std::cout << "\t\t" << operationName << "(" << stackToString(currentStackData, m_cfg) << " -> ";
		}

		// literals should have been pulled out a priori and now are treated as push constants
		// todo yulAssert(ranges::none_of(opLiveOut, IsSSACFGLiteral(m_cfg)));
		std::set<Slot> liveOutWithoutOutputsSet;
		for (const auto& valueId: opLiveOut | ranges::views::keys)
			liveOutWithoutOutputsSet.insert(valueId);
		liveOutWithoutOutputsSet -= operation.outputs;
		auto const liveOutWithoutOutputs = std::vector<Slot>(liveOutWithoutOutputsSet.begin(), liveOutWithoutOutputsSet.end());
		std::vector<Slot> requiredStackTop;
		if (auto const* call = std::get_if<SSACFG::Call>(&operation.kind))
			if (call->canContinue)
				requiredStackTop.emplace_back(FunctionReturnLabel{&call->call.get()});
		requiredStackTop += operation.inputs;

		static auto constexpr slotIsCompatible = [](Slot const& _source, Slot const& _target)
		{
			return std::holds_alternative<JunkSlot>(_target) || _source == _target;
		};
		/*auto const fun = [&](Slot const& _slot) -> bool
		{
			if (auto const* valueId = std::get_if<SSACFG::ValueId>(&_slot))
				return !liveOutWithoutOutputsSet.contains(*valueId);
			return false;
		};*/
		// auto tail = _stack.data();

		for (size_t depth = 0; depth < stack.size(); ++depth)
			if (!liveOutWithoutOutputsSet.contains(stack.slot(depth)) && ranges::find(requiredStackTop, stack.slot(depth)) == ranges::end(requiredStackTop))
				stack.declareJunk(depth);
		junkShuffler(stack);

		if (!m_junkBlockFinder.blockAllowsAdditionOfJunk(_blockId))
		{
			if constexpr(debugOutput)
				std::cout << "{ " << stackToString(std::vector(liveOutWithoutOutputs.begin(), liveOutWithoutOutputs.end()), m_cfg) << " } + " << stackToString(requiredStackTop, m_cfg) << ")\n";
			DanielShuffler<StackType>::shuffle(stack, liveOutWithoutOutputsSet, requiredStackTop);
		}
		else
		{
			if constexpr(debugOutput)
				std::cout << "{ " << stackToString(pileOfJunk<Slot>(junkTailSize(stack.data())), m_cfg) << " } + " << stackToString(requiredStackTop, m_cfg) << ")\n";
			auto const v = stack.data() | ranges::views::transform([&](auto const& _slot) -> Slot { return liveOutWithoutOutputsSet.contains(_slot) ? _slot : JunkSlot{}; }) | ranges::to<std::vector<Slot>>;
			DanielShuffler<StackType>::shuffle(stack, {}, v + requiredStackTop);
		}

		m_stackLayout[_blockId].operationIn.push_back(currentStackData);

		for (size_t i = 0; i < requiredStackTop.size(); ++i)
			stack.pop();
		for (auto const& val: operation.outputs)
			stack.push(val);
	}

	if (auto const* cjump = std::get_if<SSACFG::BasicBlock::ConditionalJump>(&block.exit))
	{
		auto const& nonZeroLiveIn = m_liveness.liveIn(cjump->nonZero);
		auto const& zeroLiveIn = m_liveness.liveIn(cjump->zero);
		//auto const nonZeroUsed = m_liveness.used(cjump->nonZero);
		//auto const zeroUsed = m_liveness.used(cjump->zero);

		SSACFGLiveness::LivenessData commonLiveOut;
		for (auto const& [liveIn, target]: { std::pair{&zeroLiveIn, cjump->zero}, std::pair{&nonZeroLiveIn, cjump->nonZero} }) {
			ReversePhiFunctionTransform transf(m_cfg, _blockId, target);
			for (auto const& [valueId, count]: *liveIn)
				commonLiveOut.insert(transf(valueId), count);
		}

		// mark all as junk that are not live
		declareJunk(stack, commonLiveOut);
		// pop everything not in the combined pre image
		// we can ignore the phi function pre-image slots because they are definitely in the combined liveness
		while (
			stack.size() > 0 &&
			std::holds_alternative<SSACFG::ValueId>(stack.top()) &&
			!commonLiveOut.contains(std::get<SSACFG::ValueId>(stack.top()))
		)
			stack.pop();
		for (auto it = stack.data().rbegin(); it != stack.data().rend(); ++it)
		{
			if (std::holds_alternative<SSACFG::ValueId>(*it) && !commonLiveOut.contains(std::get<SSACFG::ValueId>(*it)))
			{
				yulAssert(it != stack.data().rbegin()); // this shouldn't happen as we have already popped everything up front
				auto const depth = static_cast<std::size_t>(std::distance(stack.data().rbegin(), it));
				if (depth > 0)
					stack.swap(depth);
				stack.pop();
			}
		}
	}

	m_stackLayout[_blockId].stackOut = currentStackData;
	m_blockIsGenerated[_blockId.value] = true;

	if constexpr (debugOutput)
		std::cout << fmt::format("\t\tstack out = {}\n", stackToString(currentStackData, m_cfg));
}
