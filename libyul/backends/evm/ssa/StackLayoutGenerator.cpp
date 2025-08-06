#include "libyul/backends/evm/SSACFGLiveness.h"
#include "libyul/backends/evm/SSACFGStackShuffler.h"
#include "range/v3/algorithm/equal.hpp"
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

template<size_t ReachableStackDepth=16>
class OperationForwardShuffler
{
	using Stack = StackLayoutGenerator::StackType;
	using Slot = Stack::Slot;

public:
	static void shuffle(
		Stack& _stack,
		std::vector<Slot> const& _requiredTop,
		SSACFGLiveness::LivenessData const& _liveOut,
		bool _generateJunk
	)
	{
		constexpr std::size_t maxIterations = 1000;
		std::size_t i = 0;
		for (; i < maxIterations && shuffleStep(_stack, _requiredTop, _liveOut, _generateJunk); ++i) {}
		yulAssert(i < maxIterations, "Maximum iterations reached");
	}

private:
	template<ranges::range Slots>
	static std::map<Slot, size_t> histogram(Slots const& _slots)
	{
		std::map<Slot, size_t> result;
		for (auto const& slot: _slots)
		{
			auto const [it, _] = result.try_emplace(slot);
			++it->second;
		}
		return result;
	}

	struct Ops
	{
		Ops(Stack const& _stack, std::vector<Slot> const& _requiredTop, SSACFGLiveness::LivenessData const& _liveOut):
			currentCounts(histogram(_stack)),
			targetCountsHead(histogram(_requiredTop)),
			stack(_stack),
			requiredTop(_requiredTop),
			liveOut(_liveOut)
		{}

		bool canBePopped(Slot const& _slot) const
		{
			if (std::holds_alternative<ssa::JunkSlot>(_slot))
				return true;
			if (auto const* valueId = std::get_if<SSACFG::ValueId>(&_slot))
			{
				auto const headCounts = solidity::util::valueOrDefault(targetCountsHead, _slot, 0);
				if (liveOut.count(*valueId) + headCounts > 0)
					return currentCounts.at(*valueId) > headCounts + 1; // todo or it can be freely generated

				return true;
			}
			return false;
		}

		bool isCompatible(size_t _sourceDepth, size_t _targetDepth) const
		{
			if (_sourceDepth >= stack.size())
				return false;

			auto const& currentSlot = stack.slot(_sourceDepth);
			if (_targetDepth < requiredTop.size())
			{
				auto const& requiredTopSlot = *(requiredTop.rbegin() + _targetDepth);
				return std::holds_alternative<ssa::JunkSlot>(requiredTopSlot) || requiredTopSlot == currentSlot;
			}

			if (auto const* valueId = std::get_if<SSACFG::ValueId>(&currentSlot))
				return currentCounts.at(*valueId) < liveOut.count(*valueId) + solidity::util::valueOrDefault(targetCountsHead, currentSlot, 0);

			// todo this ignores junk, we might want to declare swapping junk into the tail part as compatible, too
			return false;
		}

		bool needsMoreOf(Slot const& _slot) const
		{
			auto const headCount = ranges::count_if(requiredTop, [&](auto const& _topSlot) { return _slot == _topSlot; });
			auto const tailCount = [&]() -> std::uint32_t
			{
				if (auto const* valueId = std::get_if<SSACFG::ValueId>(&_slot))
					return liveOut.count(*valueId);
				return 0;
			}();
			auto const currentCount = solidity::util::valueOrDefault(currentCounts, _slot, 0);
			if (headCount > 0)
			{
				if (currentCount == 0)
					return true;

				if (tailCount > 0)
					return currentCount <= headCount;
				return currentCount < headCount;
			}

			// if it was in the head, we already dealt with it
			yulAssert(headCount == 0);
			if (tailCount > 0 && currentCount == 0)
				return true;
			return false;
		}

		bool needsSlotBroughtUp() const
		{
			// the target top will be consumed, so if there's stuff in there that is also live out, it must occur
			// twice in the stack (in the target top region (as often as required there) and then somewhere else)
			// if there is something in target or live out that isn't on stack, that thing must be brought up (could be,
			// e.g., a push constant)
			return requiredSlot().has_value();
		}

		std::optional<Slot> requiredSlot() const
		{
			for (auto const& slot: requiredTop)
				if (needsMoreOf(slot))
					return true;
			for (const auto& slot: liveOut | ranges::views::keys)
				if (needsMoreOf(slot))
					return slot;

			return std::nullopt;
		}

		std::map<Slot, size_t> currentCounts;
		std::map<Slot, size_t> targetCountsHead;
		Stack const& stack;
		std::vector<Slot> const& requiredTop;
		SSACFGLiveness::LivenessData const& liveOut;
	};

	/// Finds a slot to dup or push with the aim of eventually fixing @a _targetOffset in the target.
	/// In the simplest case, the slot at @a _targetOffset has a multiplicity > 0, i.e. it can directly be dupped or pushed
	/// and the next iteration will fix @a _targetOffset.
	/// But, in general, there may already be enough copies of the slot that is supposed to end up at @a _targetOffset
	/// on stack, s.t. it cannot be dupped again. In that case there has to be a copy of the desired slot on stack already
	/// elsewhere that is not yet in place (`nextOffset` below). The fact that ``nextOffset`` is not in place means that
	/// we can (recursively) try bringing up the slot that is supposed to end up at ``nextOffset`` in the *target*.
	/// When the target slot at ``nextOffset`` is fixed, the current source slot at ``nextOffset`` will be
	/// at the stack top, which is the slot required at @a _targetOffset.
	static bool bringUpTargetSlot(Ops const& _ops, Stack& _stack, size_t _targetDepth)
	{
		std::list toVisit{_targetDepth};
		std::set<size_t> visited;

		while (!toVisit.empty())
		{
			auto depth = *toVisit.begin();
			toVisit.erase(toVisit.begin());
			visited.emplace(depth);

			if (depth < _ops.requiredTop.size())
			{
				auto const& slot = _ops.requiredTop[_ops.requiredTop.size() - depth - 1];
				if (_ops.needsMoreOf(slot))
				{
					_stack.pushOrDup(slot);
					return true;
				}
			}
			else
			{
				// we are no longer in the stack top, so let's just find _some_ slot that we need more of
				for (const auto& slot: _ops.liveOut | ranges::views::keys)
					if (_ops.needsMoreOf(slot))
					{
						_stack.pushOrDup(slot);
						return true;
					}
			}

			// There must be another slot we can dup/push that will lead to the target slot at ``depth`` to be fixed.
			for (auto nextDepth: ranges::views::iota(0u, std::min(_stack.size(), _ops.requiredTop.size() + 1)) | ranges::views::reverse)
				if (
					!_ops.isCompatible(nextDepth, nextDepth) &&
					_ops.isCompatible(nextDepth, depth)
				)
					if (!visited.contains(nextDepth))
						toVisit.emplace_back(nextDepth);
		}
		return false;
	}

	// If dupping an ideal slot causes a slot that will still be required to become unreachable, then dup
	// the latter slot first.
	// @returns true, if it performed a dup.
	static bool dupDeepSlotIfRequired(Ops const& _ops, Stack& _stack)
	{
		// Check if the stack is large enough for anything to potentially become unreachable.
		if (_stack.size() < ReachableStackDepth - 1)
			return false;
		// Check whether any deep slot might still be needed later (i.e. we still need to reach it with a DUP or SWAP).
		for (size_t sourceOffset: ranges::views::iota(0u, _stack.size() - (ReachableStackDepth - 1)))
		{
			auto const sourceDepth = _stack.size() - sourceOffset - 1;
			// This slot needs to be moved.
			if (!_ops.isCompatible(sourceDepth, sourceDepth))
			{
				// If the current top fixes the slot, swap it down now.
				if (_ops.isCompatible(0, sourceDepth))
				{
					_stack.swap(sourceDepth);
					return true;
				}
				// Bring up a slot to fix this now, if possible.
				if (bringUpTargetSlot(_ops, _stack, sourceDepth))
					return true;
				// Otherwise swap up the slot that will fix the offending slot.
				for (auto offset: ranges::views::iota(sourceOffset + 1, _stack.size()))
				{
					auto const depth = _stack.size() - offset - 1;
					if (_ops.isCompatible(depth, sourceDepth))
					{
						_stack.swap(depth);
						return true;
					}
				}
				// Otherwise give up - we will need stack compression or stack limit evasion.
			}
			// We need another copy of this slot.
			else if (_ops.needsMoreOf(_stack.slot(sourceDepth)))
			{
				// If this slot occurs again later, we skip this occurrence.
				if (ranges::any_of(
					ranges::views::iota(sourceOffset + 1, _stack.size()),
					[&](size_t _offset) { return _stack.slot(sourceDepth) == _stack.slot(_stack.size() - _offset - 1); }
				))
					continue;
				// Bring up the target slot that would otherwise become unreachable.
				for (size_t targetOffset: ranges::views::iota(0u, _ops.requiredTop.size()))
				{
					if (std::holds_alternative<ssa::JunkSlot>(_ops.requiredTop[targetOffset]))
						continue;
					if (_ops.isCompatible(sourceDepth, _ops.requiredTop.size() - targetOffset - 1))
					{
						_stack.pushOrDup(_ops.requiredTop[targetOffset]);
						return true;
					}
				}
			}
		}
		return false;
	}

	static bool shuffleStep(
		Stack& _stack,
		std::vector<Slot> const& _requiredTop,
		SSACFGLiveness::LivenessData const& _liveOut,
		bool const _generateJunk
	)
	{
		Ops const ops(_stack, _requiredTop, _liveOut);

		// Check if we have the required top already
		if (_requiredTop.size() <= _stack.size())
		{
			bool const topIsCorrect = ranges::equal(
				_stack.data().rbegin(), _stack.data().rbegin() + static_cast<std::ptrdiff_t>(_requiredTop.size()),
				_requiredTop.rbegin(), _requiredTop.rend()
			);

			// if the top is fine and we still have enough slots for live out, we're done
			if (topIsCorrect)
			{
				if (ops.needsSlotBroughtUp())
				{
					if (!dupDeepSlotIfRequired(ops, _stack))
						// the top is fine, so we bring up something in the tail (pointed to by requiredTop.size())
						yulAssert(bringUpTargetSlot(ops, _stack, ops.requiredTop.size()));
					return true;
				}
				return false;
			}
		}

		// If we no longer need the current stack top, we pop it
		if (ops.canBePopped(_stack.top()))
		{
			_stack.pop();
			return true;
		}

		yulAssert(_requiredTop.size() > 0, "From here on out, we need slots to be required in the top. Otherwise we should've terminated already.");

		// If the top is not supposed to be exactly what is on top right now, try to find a lower position to swap it to.
		if (!ops.isCompatible(0, 0))
			for (size_t depth: ranges::views::iota(1u, std::min(_stack.size(), _requiredTop.size() + 1)) | ranges::views::reverse)
				// It makes sense to swap to a lower position, if
				if (
					!ops.isCompatible(depth, depth) && // The lower slot is not already in position.
					_stack.slot(depth) != _stack.top() && // We would not just swap identical slots.
					ops.isCompatible(0, depth) // The lower position wants to have this slot.
				)
				{
					// We cannot swap that deep.
					if (depth > ReachableStackDepth)
					{
						// If there is a reachable slot to be removed, park the current top there.
						for (size_t swapDepth: ranges::views::iota(1u, ReachableStackDepth + 1u) | ranges::views::reverse)
							if (ops.canBePopped(_stack.slot(swapDepth)))
							{
								_stack.swap(swapDepth);
								if (std::holds_alternative<ssa::JunkSlot>(_stack.top()))
									// Usually we keep a slot that is to-be-removed, if the current top is arbitrary.
									// However, since we are in a stack-too-deep situation, pop it immediately
									// to compress the stack (we can always push back junk in the end).
									_stack.pop();
								return true;
							}
						// Otherwise, we rely on stack compression or stack-to-memory.
					}
					_stack.swap(depth);
					return true;
				}

		// If the top is not in position, try to find a slot that wants to be at the top and swap it up.
		if (!ops.isCompatible(0, 0))
			for (size_t depth: ranges::views::iota(1u, _stack.size()))
				if (
					!ops.isCompatible(depth, depth) &&
					ops.isCompatible(depth, 0)
				)
				{
					_stack.swap(depth);
					return true;
				}

		if (ops.needsSlotBroughtUp())
		{
			if (!dupDeepSlotIfRequired(ops, _stack))
				// the top is fine, so we bring up something in the tail (pointed to by requiredTop.size())
				yulAssert(bringUpTargetSlot(ops, _stack, ops.requiredTop.size()));
			return true;
		}

		yulAssert(false, "reached final and forbidden state");
	}
};

void junkShuffler(StackLayoutGenerator::StackType& _stack)
{
	// goal is to have the junk in one block at the bottom
	auto numJunk = ranges::count_if(_stack, [](auto const& _slot) { return std::holds_alternative<ssa::JunkSlot>(_slot); });
	size_t i = 0;
	while (numJunk > 0 && i < numJunk)
	{
		if (std::holds_alternative<ssa::JunkSlot>(_stack.data()[i]))
		{
			// we have a block of i junk slots at the bottom
			++i;
			continue;
		}

		if (std::holds_alternative<ssa::JunkSlot>(_stack.top()))
		{
			// todo it might be cheaper to swap or to pop
			// if we can reach the non-junk slot, swap it up, else pop the junk

			{
				_stack.pop();
				--numJunk;
				continue;
			}
		}

		// find the next best junk
		std::optional<size_t> junk(std::nullopt);
		for (size_t junkDepth = 1; junkDepth < std::min(static_cast<size_t>(17), _stack.size()); ++junkDepth)
			if (std::holds_alternative<ssa::JunkSlot>(_stack.slot(junkDepth)))
			{
				junk = junkDepth;
				break;
			}

		if (junk)
		{
			_stack.swap(*junk);
			continue;
		}

		// give up if there's no more junk in reach
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
		yulAssert(parentExits.size() == 1);
		// todo option1: shuffle junk to the bottom and/or pop it if non-junk isn't reachable
		// todo option2: pass through
		// todo option3: hard sort by usage frequency
		m_stackLayout[_blockId].stackIn = *parentExits[0].second;

		if (!block.phis.empty())
			handlePhiFunctions(m_stackLayout[_blockId].stackIn, ReversePhiFunctionTransform(m_cfg, parentExits[0].first, _blockId), m_liveness.liveIn(_blockId));

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
		auto opLiveOutWithoutOutputs = opLiveOut;
		for (auto const& output: operation.outputs)
			opLiveOutWithoutOutputs.erase(output);

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

		for (size_t depth = 0; depth < stack.size(); ++depth)
			if (!liveOutWithoutOutputsSet.contains(stack.slot(depth)) && ranges::find(requiredStackTop, stack.slot(depth)) == ranges::end(requiredStackTop))
				stack.declareJunk(depth);
		// junkShuffler(stack);*/

		// declareJunk(stack, opLiveOutWithoutOutputs );
		if constexpr(debugOutput)
			std::cout << "{ " << stackToString(std::vector(liveOutWithoutOutputs.begin(), liveOutWithoutOutputs.end()), m_cfg) << " } + " << stackToString(requiredStackTop, m_cfg) << ")" << std::flush;
		OperationForwardShuffler<>::shuffle(stack, requiredStackTop, opLiveOutWithoutOutputs, m_junkBlockFinder.blockAllowsAdditionOfJunk(_blockId));
		/*if (!m_junkBlockFinder.blockAllowsAdditionOfJunk(_blockId))
		{
			if constexpr(debugOutput)
				std::cout << "{ " << stackToString(std::vector(liveOutWithoutOutputs.begin(), liveOutWithoutOutputs.end()), m_cfg) << " } + " << stackToString(requiredStackTop, m_cfg) << ")";
			DanielShuffler<StackType>::shuffle(stack, liveOutWithoutOutputsSet, requiredStackTop);
		}
		else
		{
			if constexpr(debugOutput)
				std::cout << "{ " << stackToString(pileOfJunk<Slot>(junkTailSize(stack.data())), m_cfg) << " } + " << stackToString(requiredStackTop, m_cfg) << ")";
			auto const v = stack.data() | ranges::views::transform([&](auto const& _slot) -> Slot { return liveOutWithoutOutputsSet.contains(_slot) ? _slot : JunkSlot{}; }) | ranges::to<std::vector<Slot>>;
			DanielShuffler<StackType>::shuffle(stack, {}, v + requiredStackTop);
		}*/


		m_stackLayout[_blockId].operationIn.push_back(currentStackData);

		for (size_t i = 0; i < requiredStackTop.size(); ++i)
			stack.pop();
		for (auto const& val: operation.outputs)
			stack.push(val);

		if constexpr(debugOutput)
			fmt::print(" -> {}\n", stackToString(currentStackData, m_cfg));
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
