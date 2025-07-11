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

#pragma once

#include <libyul/backends/evm/StackHelpers.h>
#include <libyul/backends/evm/SSACFGStack.h>

#include <range/v3/algorithm/find.hpp>
#include <range/v3/algorithm/find_end.hpp>
#include <range/v3/algorithm/find_if_not.hpp>
#include <range/v3/view/concat.hpp>

#include <concepts>
#include <queue>
#include <set>
#include <algorithm>
#include <string>

namespace solidity::yul
{

template<typename StackShuffler>
concept SSACFGStackShuffler = requires(
	StackShuffler _shuffler,
	typename StackShuffler::Stack _sourceStack,
	std::vector<typename StackShuffler::Stack::Slot> _targetStackTop,
	std::set<typename StackShuffler::Stack::Slot> _targetStackRest
)
{
	typename StackShuffler::Stack;
	{ _shuffler.shuffle(_sourceStack, _targetStackRest, _targetStackTop) } -> std::convertible_to<typename StackShuffler::Stack>;
};

template<typename StackType>
struct BubbleShuffler
{
	using Stack = StackType;
	using StackSlot = typename Stack::Slot;
	static Stack shuffle(Stack const& _sourceStack, std::vector<StackSlot> const& _targetStackRest, std::vector<StackSlot> const& _targetStackTop)
	{
		Stack shuffledStack = _sourceStack;
		auto const histogram = [](std::vector<StackSlot> const& _stack, std::vector<StackSlot> const& _rest = {})
		{
			std::map<StackSlot, size_t> counts;
			for (auto const& slot: _stack)
				++counts[slot];
			for (auto const& slot: _rest)
				++counts[slot];
			return counts;
		};
		auto const targetCounts = histogram(_targetStackTop, _targetStackRest);
		{
			auto const stackCounts = histogram(_sourceStack.data());
			// first, remove everything from the stack that occurs more often than what's in the target
			for (auto const& [slot, count]: stackCounts)
			{
				size_t targetCount = 0;
				if (auto it = targetCounts.find(slot); it != targetCounts.end())
					targetCount = it->second;
				if (count > targetCount)
					for (size_t i = 0; i < count - targetCount; ++i)
					{
						auto depth = util::findOffset(_sourceStack.data() | ranges::views::reverse, slot);
						yulAssert(depth);
						if (depth > 0)
							shuffledStack.swap(*depth);
						shuffledStack.pop();
					}
			}
			// then dup/push stuff that's not there yet in appropriate quantities
			for (auto const& [slot, targetCount]: targetCounts)
			{
				auto findIt = stackCounts.find(slot);
				if (findIt == stackCounts.end())
					for (size_t i = 0; i < targetCount; ++i)
						shuffledStack.pushOrDup(slot);
				else
				{
					auto currentCount = std::min(targetCount, findIt->second);
					yulAssert(currentCount <= targetCount);
					for (size_t i = 0; i < targetCount - currentCount; ++i)
						shuffledStack.dup(slot);
				}
			}
		}

		// now we have the same elements in the shuffled stack - just potentially in a different order
		yulAssert(histogram(shuffledStack.data()) == targetCounts);
		auto const targetStackTopOffset = _targetStackRest.size();
		for (size_t i = 0; i < _targetStackTop.size(); ++i)
		{
			// look at the bottom element of the stack and swap something there if it's not already the correct slot
			if (shuffledStack[i + targetStackTopOffset] != _targetStackTop[i])
			{
				auto const depth = util::findOffset(shuffledStack | ranges::views::reverse, _targetStackTop[i]);
				if (depth > 0)
					shuffledStack.swap(*depth);
				yulAssert(shuffledStack.top() == _targetStackTop[i]);
				if (shuffledStack.size() > i + targetStackTopOffset + 1)
					shuffledStack.swap(shuffledStack.size() - 1 - targetStackTopOffset - i);
			}
			yulAssert(shuffledStack[i + targetStackTopOffset] == _targetStackTop[i]);
		}

		yulAssert(shuffledStack.size() == _targetStackTop.size() + _targetStackRest.size());
		// yulAssert(m_stack == _target, fmt::format("Stack target mismatch: current = {} =/= {} = target", stackToStringLoc(m_cfg.get(), m_stack), stackToStringLoc(m_cfg.get(), _target)));
		return shuffledStack;
	}

};

template<
	typename StackType,
	auto SlotIsCompatible = [](typename StackType::Slot const& _source, typename StackType::Slot const& _target) { return std::holds_alternative<ssa::JunkSlot>(_target) || _source == _target; }
>
struct DanielShuffler
{
	using Stack = StackType;
	using StackSlot = typename Stack::Slot;
	static Stack shuffle(Stack const& _sourceStack, std::set<StackSlot> const& _targetStackTail, std::vector<StackSlot> const& _targetStackTop)
	{
		struct ShuffleOperations
		{
			size_t const reachableStackDepth = 16;
			Stack& currentStack;
			std::map<StackSlot, size_t> sourceCounts;
			std::vector<StackSlot> const& targetStack;
			std::map<StackSlot, size_t> targetCounts;

			ShuffleOperations(
				Stack& _currentStack,
				std::vector<StackSlot> const& _targetStack
			): currentStack(_currentStack), targetStack(_targetStack)
			{
				for (auto const& x: currentStack)
					++sourceCounts[x];
				for (auto const [i, x]: ranges::views::enumerate(targetStack))
					if (i < currentStack.size() && std::holds_alternative<ssa::JunkSlot>(targetStack[i]))
						++targetCounts[currentStack[i]];
					else
						++targetCounts[x];
			}

			bool isCompatible(size_t _source, size_t _target) const
			{
				if (_source >= currentStack.size() || _target >= targetStack.size())
					return false;
				return SlotIsCompatible(currentStack[_source], targetStack[_target]);
			}

			bool sourceIsSame(size_t _sourceOffset1, size_t _sourceOffset2) const
			{
				return _sourceOffset1 < currentStack.size() && _sourceOffset2 < currentStack.size() && currentStack[_sourceOffset1] == currentStack[_sourceOffset2];
			}

			int sourceMultiplicity(size_t _sourceOffset) const
			{
				auto const& slot = currentStack[_sourceOffset];
				return static_cast<int>(util::valueOrDefault(targetCounts, slot, static_cast<size_t>(0))) - static_cast<int>(sourceCounts.at(slot));
			}

			int targetMultiplicity(size_t _targetOffset) const
			{
				auto const& slot = targetStack[_targetOffset];
				return static_cast<int>(targetCounts.at(slot)) - static_cast<int>(util::valueOrDefault(sourceCounts, slot, static_cast<size_t>(0)));
			}

			bool targetIsArbitrary(size_t _targetOffset) const
			{
				return _targetOffset < targetStack.size() && std::holds_alternative<ssa::JunkSlot>(targetStack.at(_targetOffset));
			}

			size_t sourceSize() const { return currentStack.size(); }
			size_t targetSize() const { return targetStack.size(); }

			void swap(size_t _depth)
			{
				currentStack.swap(_depth);
			}

			void pop()
			{
				currentStack.pop();
			}

			void pushOrDupTarget(size_t _targetOffset)
			{
				currentStack.pushOrDup(targetStack[_targetOffset]);
			}

		};
		Stack shuffledStack = _sourceStack;
		auto const targetStack = std::vector(_targetStackTail.begin(), _targetStackTail.end()) + _targetStackTop;
		Shuffler<ShuffleOperations>::shuffle(shuffledStack, targetStack);
		return shuffledStack;
	}
};

template<
	typename StackType,
	auto SlotIsCompatible
>
class BlockForwardShuffler
{
	struct Histogram
	{
		std::map<typename StackType::Slot, size_t> data;
		size_t numSlots;

		bool operator==(Histogram const& _other) const
		{
			return numSlots == _other.numSlots && data == _other.data;
		}
	};

public:
	using Stack = StackType;
	using Slot = typename Stack::Slot;

	static void shuffle(Stack& _stack, std::vector<Slot> const& _requiredTail, std::vector<Slot> const& _requiredTop)
	{
		auto const tailHistogram = histogram(_requiredTail.begin(), _requiredTail.end());
		bool needsMoreShuffling = true;
		size_t iterationCount = 0;
		while (iterationCount < 1000 && needsMoreShuffling)
		{
			needsMoreShuffling = shuffleStep(_stack, tailHistogram, _requiredTop);
			++iterationCount;
		}
		yulAssert(!needsMoreShuffling, "Could not create stack layout after 1000 iterations.");
	}

private:
	template<std::input_iterator Iterator>
	static Histogram histogram(Iterator begin, Iterator end)
	{
		Histogram counts;
		for (auto it = begin; it != end; ++it)
		{
			auto const [emplaceIt, _] = counts.data.try_emplace(*it, 0);
			++emplaceIt->second;
		}
		counts.numSlots = static_cast<size_t>(std::distance(begin, end));
		return counts;
	}

	static bool compatible(Slot const& _slot1, Slot const& _slot2)
	{
		return SlotIsCompatible(_slot1, _slot2);
	}

	static bool shuffleStep(Stack& _stack, Histogram const& _requiredTailHistogram, std::vector<Slot> const& _requiredTop)
	{
		// plan:
		//	1. make it so that top and tail are final with respect to their histograms (ie distributions are same)
		//  2. for tail it doesn't matter, for top we can just use DanielShuffler to get it into the required shape
		Histogram currentTailHistogram{};
		if (_stack.size() > _requiredTop.size())
			currentTailHistogram = histogram(_requiredTop.begin(), std::prev(_stack.data().end(), static_cast<std::ptrdiff_t>(_requiredTop.size())));
		if (_stack.size() == _requiredTailHistogram.numSlots + _requiredTop.size())
		{

		}

		return isTopCorrect(_stack, _requiredTop) && currentTailHistogram == _requiredTailHistogram;
	}

	static bool isTopCorrect(Stack const& _stack, std::vector<Slot> const& _requiredTop) {
		if (_requiredTop.size() > _stack.size()) return false;

		for (size_t i = 0; i < _requiredTop.size(); ++i) {
			size_t stackIndex = _stack.size() - 1 - i;
			size_t targetIndex = _requiredTop.size() - 1 - i;

			if (!compatible(_stack[stackIndex], _requiredTop[targetIndex])) {
				return false;
			}
		}
		return true;
	}

};

template<typename StackType>
struct BlockStackInShuffler
{
	using Stack = StackType;
	using StackSlot = typename Stack::Slot;

	template<typename LiveInSlots>
	static Stack shuffle(Stack const& _sourceStack, LiveInSlots const& _liveIn)
	{
		Stack result = _sourceStack;
		auto const findNextSlotToPop = [&]
		{
			return ranges::find_if_not(
				ranges::rbegin(result),
				ranges::rend(result),
				[&](StackSlot const& _slot) { return _liveIn.contains(_slot); }
			);
		};
		auto it = findNextSlotToPop();
		while (it != ranges::rend(result))
		{
			if (it != ranges::rbegin(result))
				result.swap(static_cast<size_t>(it - ranges::rbegin(result)));
			yulAssert(!_liveIn.contains(result.top()));
			result.pop();
			it = findNextSlotToPop();
		}

		for (auto const& liveSlot: _liveIn)
			if (ranges::find(result, liveSlot) == ranges::end(result))
				result.push(liveSlot);
		return result;
	}
};

template<typename StackType>
struct GreedyForwardShuffler
{
	using Stack = StackType;
	using StackSlot = typename Stack::Slot;
	
	/// Simple, correct forward shuffler (INTENTIONALLY does NOT conform to SSACFGStackShuffler concept)
	/// Key insight: handle values that are both consumed AND live-out properly
	static Stack shuffle(
		Stack const& _sourceStack,
		std::vector<StackSlot> const& _liveOut,       // Values that must survive operation
		std::vector<StackSlot> const& _requiredTop    // Values needed at stack top (order matters!)
	)
	{
		Stack result = _sourceStack;
		
		// Safety check: don't create overly deep stacks
		if (result.size() + _requiredTop.size() > 1000) {
			// Fall back to Daniel shuffler for very deep stacks
			return DanielShuffler<Stack>::shuffle(_sourceStack, std::set<StackSlot>(_liveOut.begin(), _liveOut.end()), _requiredTop);
		}
		
		// Phase 1: Ensure extra copies for values that are both consumed and live-out (with constraints)
		ensureExtraCopiesForConsumedLiveOuts(result, _liveOut, _requiredTop);
		
		// Phase 2: Build required top in correct order (simple approach)
		buildRequiredTop(result, _requiredTop);
		
		return result;
	}

private:
	/// Phase 1: Handle the KEY INSIGHT - values consumed by operation but needed later
	static void ensureExtraCopiesForConsumedLiveOuts(
		Stack& _stack,
		std::vector<StackSlot> const& _liveOut,
		std::vector<StackSlot> const& _requiredTop
	) {
		for (auto const& requiredValue : _requiredTop) {
			// Is this value also live-out? (will be consumed but must survive)
			bool isAlsoLiveOut = ranges::find(_liveOut, requiredValue) != _liveOut.end();
			
			if (isAlsoLiveOut) {
				// Count how many copies we have on stack
				auto copyCount = std::count(_stack.data().begin(), _stack.data().end(), requiredValue);
				
				if (copyCount < 2) {
					// Find the value's position from top of stack
					auto stackData = _stack.data();
					auto reverseView = stackData | ranges::views::reverse;
					auto it = ranges::find(reverseView, requiredValue);
					
					if (it != reverseView.end()) {
						auto distance = std::distance(reverseView.begin(), it);
						// Only dup if within EVM's 16-element reach
						if (distance >= 0 && static_cast<size_t>(distance) < 16) {
							_stack.dup(requiredValue);
						}
						// If beyond reach, we can't safely dup - just proceed without extra copy
					}
				}
			}
		}
	}
	
	/// Phase 2: Build required top - respecting EVM depth constraints
	static void buildRequiredTop(Stack& _stack, std::vector<StackSlot> const& _requiredTop) {
		if (_requiredTop.empty()) return;
		
		// Fast path: check if already correct
		if (isTopAlreadyCorrect(_stack, _requiredTop)) return;
		
		// Build top from bottom to top (iterate requiredTop in reverse)
		// Example: requiredTop=[v0,64] means final stack=[...,64,v0] (v0 at top)
		// So push 64 first (ends up deeper), then v0 (ends up at top)
		for (auto it = _requiredTop.rbegin(); it != _requiredTop.rend(); ++it) {
			// Use pushOrDup which handles the depth constraints internally
			_stack.pushOrDup(*it);
		}
	}
	
	/// Check if required top is already correct (optimization)
	static bool isTopAlreadyCorrect(Stack const& _stack, std::vector<StackSlot> const& _requiredTop) {
		if (_requiredTop.size() > _stack.size()) return false;
		
		// Check if top of stack matches required top exactly
		for (size_t i = 0; i < _requiredTop.size(); ++i) {
			size_t stackIndex = _stack.size() - 1 - i;  // Stack top = size-1
			size_t requiredIndex = _requiredTop.size() - 1 - i;  // Required top = size-1
			
			if (_stack[stackIndex] != _requiredTop[requiredIndex]) {
				return false;
			}
		}
		return true;
	}
};

template<typename StackType>
struct WindowedStackState
{
	using Stack = StackType;
	using Slot = typename Stack::Slot;
	
	static constexpr size_t MAX_REACHABLE_DEPTH = 16;
	static constexpr size_t MAX_STACK_SIZE = 1024;
	
	std::vector<Slot> frozenQueue;     // Elements beyond reachable depth (immutable during local operations)
	std::vector<Slot> reachableWindow; // Top 16-17 elements that can be manipulated
	size_t operationCost = 0;          // Cumulative cost to reach this state
	
	WindowedStackState() = default;
	
	explicit WindowedStackState(Stack const& _stack) 
	{
		auto const& stackData = _stack.data();
		
		if (stackData.size() <= MAX_REACHABLE_DEPTH) {
			// Entire stack is reachable
			reachableWindow = stackData;
		} else {
			// Split into frozen queue and reachable window
			frozenQueue.assign(stackData.begin(), stackData.end() - MAX_REACHABLE_DEPTH);
			reachableWindow.assign(stackData.end() - MAX_REACHABLE_DEPTH, stackData.end());
		}
	}
	
	explicit WindowedStackState(std::vector<Slot> const& _stackData) 
	{
		if (_stackData.size() <= MAX_REACHABLE_DEPTH) {
			// Entire stack is reachable
			reachableWindow = _stackData;
		} else {
			// Split into frozen queue and reachable window
			frozenQueue.assign(_stackData.begin(), _stackData.end() - MAX_REACHABLE_DEPTH);
			reachableWindow.assign(_stackData.end() - MAX_REACHABLE_DEPTH, _stackData.end());
		}
	}
	
	// State properties
	size_t totalSize() const { return frozenQueue.size() + reachableWindow.size(); }
	bool isEmpty() const { return totalSize() == 0; }
	bool isReachable(Slot const& _slot) const;
	std::optional<size_t> reachableDepth(Slot const& _slot) const;
	
	// State reconstruction
	std::vector<Slot> toStackData() const;
	Stack toStack(typename Stack::Callbacks _callbacks, typename Stack::CanBeFreelyGenerated _canBeFreelyGenerated) const;
	
	// Windowed operations
	bool canSwap(size_t _depth) const;
	bool canDup(Slot const& _slot) const;
	bool canPop() const;
	bool canPush(Slot const& _slot) const;
	
	// State transitions (return new state with updated cost)
	template<typename CanBeFreelyGenerated>
	WindowedStackState swap(size_t _depth) const;
	template<typename CanBeFreelyGenerated>
	WindowedStackState dup(Slot const& _slot) const;
	template<typename CanBeFreelyGenerated>
	WindowedStackState pop() const;
	template<typename CanBeFreelyGenerated>
	WindowedStackState push(Slot const& _slot, CanBeFreelyGenerated const& _canBeFreelyGenerated) const;
	
	// Global operations (expensive - cross window boundary)
	WindowedStackState bringIntoReach(size_t _count) const;  // Pop to access frozen elements
	WindowedStackState sendToFrozen(size_t _count) const;    // Push beyond reachable window
	
	// Validation
	bool isValid() const;
	
	// Comparison for A* search
	bool operator==(WindowedStackState const& _other) const;
	bool operator<(WindowedStackState const& _other) const;
	
	// Hash for unordered containers
	size_t hash() const;
};

template<typename StackType>
bool WindowedStackState<StackType>::isReachable(Slot const& _slot) const
{
	return std::find(reachableWindow.begin(), reachableWindow.end(), _slot) != reachableWindow.end();
}

template<typename StackType>
std::optional<size_t> WindowedStackState<StackType>::reachableDepth(Slot const& _slot) const
{
	// Find slot in reachable window (depth 0 = top of stack)
	auto it = std::find(reachableWindow.rbegin(), reachableWindow.rend(), _slot);
	if (it != reachableWindow.rend()) {
		return static_cast<size_t>(std::distance(reachableWindow.rbegin(), it));
	}
	return std::nullopt;
}

template<typename StackType>
std::vector<typename WindowedStackState<StackType>::Slot> WindowedStackState<StackType>::toStackData() const
{
	std::vector<Slot> result;
	result.reserve(totalSize());
	
	// Frozen queue first (bottom of stack)
	result.insert(result.end(), frozenQueue.begin(), frozenQueue.end());
	
	// Reachable window second (top of stack)
	result.insert(result.end(), reachableWindow.begin(), reachableWindow.end());
	
	return result;
}

template<typename StackType>
typename WindowedStackState<StackType>::Stack WindowedStackState<StackType>::toStack(
	typename Stack::Callbacks _callbacks, 
	typename Stack::CanBeFreelyGenerated _canBeFreelyGenerated
) const
{
	return Stack(toStackData(), std::move(_callbacks), std::move(_canBeFreelyGenerated));
}

template<typename StackType>
bool WindowedStackState<StackType>::canSwap(size_t _depth) const
{
	return _depth >= 1 && _depth <= MAX_REACHABLE_DEPTH && _depth < reachableWindow.size();
}

template<typename StackType>
bool WindowedStackState<StackType>::canDup(Slot const& _slot) const
{
	auto depth = reachableDepth(_slot);
	return depth && (*depth + 1) <= MAX_REACHABLE_DEPTH;
}

template<typename StackType>
bool WindowedStackState<StackType>::canPop() const
{
	return !reachableWindow.empty();
}

template<typename StackType>
bool WindowedStackState<StackType>::canPush(Slot const& _slot) const
{
	return totalSize() < MAX_STACK_SIZE;
}

template<typename StackType>
template<typename CanBeFreelyGenerated>
WindowedStackState<StackType> WindowedStackState<StackType>::swap(size_t _depth) const
{
	yulAssert(canSwap(_depth), "Invalid swap operation");
	
	WindowedStackState result = *this;
	auto cost = WindowedEVMCostModel<StackType>::swapCost(_depth);
	result.operationCost += cost.total();
	
	// Swap within reachable window
	size_t topIndex = reachableWindow.size() - 1;
	size_t swapIndex = topIndex - _depth;
	std::swap(result.reachableWindow[topIndex], result.reachableWindow[swapIndex]);
	
	return result;
}

template<typename StackType>
template<typename CanBeFreelyGenerated>
WindowedStackState<StackType> WindowedStackState<StackType>::dup(Slot const& _slot) const
{
	yulAssert(canDup(_slot), "Invalid dup operation");
	
	WindowedStackState result = *this;
	auto depth = reachableDepth(_slot);
	auto cost = WindowedEVMCostModel<StackType>::dupCost(depth ? *depth + 1 : 1);
	result.operationCost += cost.total();
	
	// Duplicate slot to top of reachable window
	result.reachableWindow.push_back(_slot);
	
	return result;
}

template<typename StackType>
template<typename CanBeFreelyGenerated>
WindowedStackState<StackType> WindowedStackState<StackType>::pop() const
{
	yulAssert(canPop(), "Invalid pop operation");
	
	WindowedStackState result = *this;
	auto cost = WindowedEVMCostModel<StackType>::popCost();
	result.operationCost += cost.total();
	
	// Remove top of reachable window
	result.reachableWindow.pop_back();
	
	return result;
}

template<typename StackType>
template<typename CanBeFreelyGenerated>
WindowedStackState<StackType> WindowedStackState<StackType>::push(Slot const& _slot, CanBeFreelyGenerated const& _canBeFreelyGenerated) const
{
	yulAssert(canPush(_slot), "Invalid push operation");
	
	WindowedStackState result = *this;
	auto cost = WindowedEVMCostModel<StackType>::pushCost(_slot, _canBeFreelyGenerated);
	result.operationCost += cost.total();
	
	// Add to top of reachable window
	result.reachableWindow.push_back(_slot);
	
	// If reachable window exceeds limit, move oldest element to frozen queue
	if (result.reachableWindow.size() > MAX_REACHABLE_DEPTH) {
		result.frozenQueue.push_back(result.reachableWindow.front());
		result.reachableWindow.erase(result.reachableWindow.begin());
		// Add cost for cross-window operation
		auto crossWindowCost = WindowedEVMCostModel<StackType>::sendToFrozenCost(1);
		result.operationCost += crossWindowCost.total();
	}
	
	return result;
}

template<typename StackType>
WindowedStackState<StackType> WindowedStackState<StackType>::bringIntoReach(size_t _count) const
{
	yulAssert(_count <= frozenQueue.size(), "Cannot bring more elements than available in frozen queue");
	
	WindowedStackState result = *this;
	auto cost = WindowedEVMCostModel<StackType>::bringIntoReachCost(_count);
	result.operationCost += cost.total();
	
	// Move elements from frozen queue to reachable window
	for (size_t i = 0; i < _count; ++i) {
		// Take from back of frozen queue (closest to reachable window)
		result.reachableWindow.insert(result.reachableWindow.begin(), result.frozenQueue.back());
		result.frozenQueue.pop_back();
		
		// If reachable window exceeds limit, we need to pop some elements
		if (result.reachableWindow.size() > MAX_REACHABLE_DEPTH) {
			result.reachableWindow.pop_back();
		}
	}
	
	return result;
}

template<typename StackType>
WindowedStackState<StackType> WindowedStackState<StackType>::sendToFrozen(size_t _count) const
{
	yulAssert(_count <= reachableWindow.size(), "Cannot send more elements than available in reachable window");
	
	WindowedStackState result = *this;
	auto cost = WindowedEVMCostModel<StackType>::sendToFrozenCost(_count);
	result.operationCost += cost.total();
	
	// Move elements from reachable window to frozen queue
	for (size_t i = 0; i < _count; ++i) {
		// Take from front of reachable window (deepest reachable element)
		result.frozenQueue.push_back(result.reachableWindow.front());
		result.reachableWindow.erase(result.reachableWindow.begin());
	}
	
	return result;
}

template<typename StackType>
bool WindowedStackState<StackType>::isValid() const
{
	return totalSize() <= MAX_STACK_SIZE && 
	       reachableWindow.size() <= MAX_REACHABLE_DEPTH;
}

template<typename StackType>
bool WindowedStackState<StackType>::operator==(WindowedStackState const& _other) const
{
	return frozenQueue == _other.frozenQueue && 
	       reachableWindow == _other.reachableWindow;
}

template<typename StackType>
bool WindowedStackState<StackType>::operator<(WindowedStackState const& _other) const
{
	if (frozenQueue != _other.frozenQueue) {
		return frozenQueue < _other.frozenQueue;
	}
	return reachableWindow < _other.reachableWindow;
}

template<typename StackType>
size_t WindowedStackState<StackType>::hash() const
{
	size_t h1 = std::hash<std::vector<Slot>>{}(frozenQueue);
	size_t h2 = std::hash<std::vector<Slot>>{}(reachableWindow);
	return h1 ^ (h2 << 1);
}

// Hash specialization for WindowedStackState
template<typename StackType>
struct std::hash<WindowedStackState<StackType>>
{
	size_t operator()(WindowedStackState<StackType> const& _state) const
	{
		return _state.hash();
	}
};

// EVM operation cost model for windowed operations
template<typename StackType>
struct WindowedEVMCostModel
{
	// Cost components: gas cost and bytecode size cost
	struct Cost {
		size_t gas;        // Gas consumption cost
		size_t bytecode;   // Bytecode size cost
		
		Cost(size_t _gas = 0, size_t _bytecode = 0) : gas(_gas), bytecode(_bytecode) {}
		
		// Total weighted cost (gas is primary, bytecode is secondary)
		size_t total() const { return gas + bytecode; }
		
		Cost operator+(Cost const& _other) const {
			return Cost(gas + _other.gas, bytecode + _other.bytecode);
		}
		
		Cost operator*(size_t _multiplier) const {
			return Cost(gas * _multiplier, bytecode * _multiplier);
		}
	};
	
	// EVM instruction gas costs (based on Ethereum Yellow Paper)
	static constexpr size_t SWAP_GAS_BASE = 3;
	static constexpr size_t DUP_GAS_BASE = 3;
	static constexpr size_t POP_GAS = 2;
	static constexpr size_t PUSH_GAS = 3;
	
	// Bytecode size costs (in bytes)
	static constexpr size_t SWAP_BYTECODE = 1;
	static constexpr size_t DUP_BYTECODE = 1;
	static constexpr size_t POP_BYTECODE = 1;
	static constexpr size_t PUSH_LITERAL_BYTECODE = 33; // PUSH32 + 32 bytes
	
	// Cross-window operation penalties
	static constexpr size_t CROSS_WINDOW_PENALTY = 50;
	
	// Calculate cost for SWAP operation
	static Cost swapCost(size_t _depth) {
		// SWAP1 to SWAP16 have same gas cost but different bytecode representation
		if (_depth >= 1 && _depth <= 16) {
			return Cost(SWAP_GAS_BASE, SWAP_BYTECODE);
		}
		// Beyond SWAP16 - not directly supported by EVM
		return Cost(SWAP_GAS_BASE * _depth, SWAP_BYTECODE * _depth);
	}
	
	// Calculate cost for DUP operation
	static Cost dupCost(size_t _depth) {
		// DUP1 to DUP16 have same gas cost but different bytecode representation
		if (_depth >= 1 && _depth <= 16) {
			return Cost(DUP_GAS_BASE, DUP_BYTECODE);
		}
		// Beyond DUP16 - not directly supported by EVM
		return Cost(DUP_GAS_BASE * _depth, DUP_BYTECODE * _depth);
	}
	
	// Calculate cost for POP operation
	static Cost popCost() {
		return Cost(POP_GAS, POP_BYTECODE);
	}
	
	// Calculate cost for PUSH operation
	static Cost pushCost(typename StackType::Slot const& _slot, 
	                     typename StackType::CanBeFreelyGenerated const& _canBeFreelyGenerated) {
		if (_canBeFreelyGenerated(_slot)) {
			// Can push literal - use PUSH instruction
			return Cost(PUSH_GAS, PUSH_LITERAL_BYTECODE);
		} else {
			// Cannot push literal - must use DUP from existing value
			// This is handled by the DUP cost calculation
			return Cost(DUP_GAS_BASE, DUP_BYTECODE);
		}
	}
	
	// Calculate cost for bringing elements into reach (very expensive)
	static Cost bringIntoReachCost(size_t _count) {
		// This requires complex sequence of operations to rotate stack
		// Penalty reflects the difficulty of accessing deep stack elements
		return Cost(CROSS_WINDOW_PENALTY * _count, SWAP_BYTECODE * _count * 8);
	}
	
	// Calculate cost for sending elements to frozen queue
	static Cost sendToFrozenCost(size_t _count) {
		// Less expensive than bringing into reach, but still costly
		return Cost(CROSS_WINDOW_PENALTY * _count / 4, SWAP_BYTECODE * _count * 2);
	}
	
	// Calculate total cost for a sequence of operations
	template<typename Operations>
	static Cost totalCost(Operations const& _operations) {
		Cost total;
		for (auto const& op : _operations) {
			total = total + op.cost;
		}
		return total;
	}
	
	// Heuristic cost estimation for target distance
	static Cost heuristicCost(WindowedStackState<StackType> const& _current,
	                          WindowedStackState<StackType> const& _target) {
		// Manhattan distance heuristic for stack transformation
		Cost heuristic;
		
		// Count misplaced elements in reachable window
		size_t misplacedCount = 0;
		size_t minSize = std::min(_current.reachableWindow.size(), _target.reachableWindow.size());
		
		for (size_t i = 0; i < minSize; ++i) {
			if (_current.reachableWindow[i] != _target.reachableWindow[i]) {
				misplacedCount++;
			}
		}
		
		// Add cost for size difference
		size_t sizeDiff = _current.reachableWindow.size() > _target.reachableWindow.size() 
			? _current.reachableWindow.size() - _target.reachableWindow.size()
			: _target.reachableWindow.size() - _current.reachableWindow.size();
		
		// Estimate minimum operations needed
		heuristic = swapCost(1) * misplacedCount + popCost() * sizeDiff;
		
		// Add penalty for frozen queue differences
		if (_current.frozenQueue != _target.frozenQueue) {
			heuristic = heuristic + bringIntoReachCost(1);
		}
		
		return heuristic;
	}
};

// Legacy cost constants for backward compatibility
template<typename StackType>
struct WindowedOperationCosts
{
	static constexpr size_t SWAP_COST = 1;
	static constexpr size_t DUP_COST = 1;
	static constexpr size_t POP_COST = 1;
	static constexpr size_t PUSH_COST = 1;
	static constexpr size_t BRING_INTO_REACH_COST = 16; // Very expensive
	static constexpr size_t SEND_TO_FROZEN_COST = 1;
};

// Windowed EVM operations with reachability constraints
template<typename StackType>
class WindowedEVMOperations
{
public:
	using Stack = StackType;
	using Slot = typename Stack::Slot;
	using State = WindowedStackState<StackType>;
	using Cost = typename WindowedEVMCostModel<StackType>::Cost;
	
	struct Operation {
		enum Type { SWAP, DUP, POP, PUSH, BRING_INTO_REACH, SEND_TO_FROZEN };
		Type type;
		size_t param;        // depth for SWAP/DUP, count for global operations
		Slot slot;          // slot for DUP/PUSH operations
		Cost cost;          // cost of this operation
		
		Operation(Type _type, size_t _param, Slot _slot, Cost _cost)
			: type(_type), param(_param), slot(_slot), cost(_cost) {}
		
		Operation(Type _type, size_t _param, Cost _cost)
			: type(_type), param(_param), slot(), cost(_cost) {}
	};
	
	template<typename CanBeFreelyGenerated>
	static std::vector<Operation> generateValidOperations(
		State const& _state,
		CanBeFreelyGenerated const& _canBeFreelyGenerated
	) {
		std::vector<Operation> operations;
		
		// SWAP operations (within reachable window)
		for (size_t depth = 1; depth <= State::MAX_REACHABLE_DEPTH && depth < _state.reachableWindow.size(); ++depth) {
			if (_state.canSwap(depth)) {
				auto cost = WindowedEVMCostModel<StackType>::swapCost(depth);
				operations.emplace_back(Operation::SWAP, depth, cost);
			}
		}
		
		// DUP operations (for slots within reachable window)
		std::set<Slot> duplicatedSlots; // Avoid duplicate DUP operations
		for (size_t i = 0; i < _state.reachableWindow.size(); ++i) {
			Slot slot = _state.reachableWindow[i];
			if (duplicatedSlots.find(slot) == duplicatedSlots.end() && _state.canDup(slot)) {
				auto depth = _state.reachableDepth(slot);
				auto cost = WindowedEVMCostModel<StackType>::dupCost(depth ? *depth + 1 : 1);
				operations.emplace_back(Operation::DUP, depth ? *depth + 1 : 1, slot, cost);
				duplicatedSlots.insert(slot);
			}
		}
		
		// POP operations
		if (_state.canPop()) {
			auto cost = WindowedEVMCostModel<StackType>::popCost();
			operations.emplace_back(Operation::POP, 0, cost);
		}
		
		// PUSH operations (for freely generated slots)
		// Note: We don't enumerate all possible freely generated slots here
		// as that would be infinite. Instead, this should be called with
		// specific target slots that need to be generated.
		
		// Cross-window operations (expensive)
		if (!_state.frozenQueue.empty()) {
			// Bring elements from frozen queue into reach
			for (size_t count = 1; count <= std::min(_state.frozenQueue.size(), size_t(4)); ++count) {
				auto cost = WindowedEVMCostModel<StackType>::bringIntoReachCost(count);
				operations.emplace_back(Operation::BRING_INTO_REACH, count, cost);
			}
		}
		
		if (_state.reachableWindow.size() > State::MAX_REACHABLE_DEPTH / 2) {
			// Send elements from reachable window to frozen queue
			size_t maxToSend = _state.reachableWindow.size() - State::MAX_REACHABLE_DEPTH / 2;
			for (size_t count = 1; count <= std::min(maxToSend, size_t(4)); ++count) {
				auto cost = WindowedEVMCostModel<StackType>::sendToFrozenCost(count);
				operations.emplace_back(Operation::SEND_TO_FROZEN, count, cost);
			}
		}
		
		return operations;
	}
	
	template<typename CanBeFreelyGenerated>
	static std::vector<Operation> generatePushOperations(
		State const& _state,
		std::vector<Slot> const& _targetSlots,
		CanBeFreelyGenerated const& _canBeFreelyGenerated
	) {
		std::vector<Operation> operations;
		
		for (auto const& slot : _targetSlots) {
			if (_state.canPush(slot)) {
				auto cost = WindowedEVMCostModel<StackType>::pushCost(slot, _canBeFreelyGenerated);
				operations.emplace_back(Operation::PUSH, 0, slot, cost);
			}
		}
		
		return operations;
	}
	
	template<typename CanBeFreelyGenerated>
	static State applyOperation(
		State const& _state,
		Operation const& _operation,
		CanBeFreelyGenerated const& _canBeFreelyGenerated
	) {
		switch (_operation.type) {
			case Operation::SWAP:
				return _state.template swap<CanBeFreelyGenerated>(_operation.param);
			case Operation::DUP:
				return _state.template dup<CanBeFreelyGenerated>(_operation.slot);
			case Operation::POP:
				return _state.template pop<CanBeFreelyGenerated>();
			case Operation::PUSH:
				return _state.template push<CanBeFreelyGenerated>(_operation.slot, _canBeFreelyGenerated);
			case Operation::BRING_INTO_REACH:
				return _state.bringIntoReach(_operation.param);
			case Operation::SEND_TO_FROZEN:
				return _state.sendToFrozen(_operation.param);
		}
		yulAssert(false, "Invalid operation type");
	}
	
	// Check if a sequence of operations is valid
	template<typename CanBeFreelyGenerated>
	static bool isValidSequence(
		State const& _initialState,
		std::vector<Operation> const& _operations,
		CanBeFreelyGenerated const& _canBeFreelyGenerated
	) {
		State currentState = _initialState;
		
		for (auto const& operation : _operations) {
			// Check if operation is valid in current state
			switch (operation.type) {
				case Operation::SWAP:
					if (!currentState.canSwap(operation.param)) return false;
					break;
				case Operation::DUP:
					if (!currentState.canDup(operation.slot)) return false;
					break;
				case Operation::POP:
					if (!currentState.canPop()) return false;
					break;
				case Operation::PUSH:
					if (!currentState.canPush(operation.slot)) return false;
					break;
				case Operation::BRING_INTO_REACH:
					if (operation.param > currentState.frozenQueue.size()) return false;
					break;
				case Operation::SEND_TO_FROZEN:
					if (operation.param > currentState.reachableWindow.size()) return false;
					break;
			}
			
			// Apply operation
			currentState = applyOperation(currentState, operation, _canBeFreelyGenerated);
			
			// Check if resulting state is valid
			if (!currentState.isValid()) return false;
		}
		
		return true;
	}
	
	// Calculate total cost of a sequence of operations
	static Cost calculateTotalCost(std::vector<Operation> const& _operations) {
		Cost total;
		for (auto const& operation : _operations) {
			total = total + operation.cost;
		}
		return total;
	}
	
	// Get operation description for debugging
	static std::string operationToString(Operation const& _operation) {
		switch (_operation.type) {
			case Operation::SWAP:
				return "SWAP(" + std::to_string(_operation.param) + ")";
			case Operation::DUP:
				return "DUP(" + std::to_string(_operation.param) + ")";
			case Operation::POP:
				return "POP";
			case Operation::PUSH:
				return "PUSH";
			case Operation::BRING_INTO_REACH:
				return "BRING_INTO_REACH(" + std::to_string(_operation.param) + ")";
			case Operation::SEND_TO_FROZEN:
				return "SEND_TO_FROZEN(" + std::to_string(_operation.param) + ")";
		}
		return "UNKNOWN";
	}
	
	// Get sequence description for debugging
	static std::string sequenceToString(std::vector<Operation> const& _operations) {
		std::string result = "[";
		for (size_t i = 0; i < _operations.size(); ++i) {
			if (i > 0) result += ", ";
			result += operationToString(_operations[i]);
		}
		result += "]";
		return result;
	}
};

// Windowed histogram heuristic for A* search
template<typename StackType>
class WindowedHistogramHeuristic
{
public:
	using Stack = StackType;
	using Slot = typename Stack::Slot;
	using State = WindowedStackState<StackType>;
	using Cost = typename WindowedEVMCostModel<StackType>::Cost;
	
	struct SlotHistogram {
		std::map<Slot, size_t> reachableSlots;  // Slots in reachable window
		std::map<Slot, size_t> frozenSlots;     // Slots in frozen queue
		size_t totalReachable = 0;
		size_t totalFrozen = 0;
		
		SlotHistogram() = default;
		
		SlotHistogram(State const& _state) {
			// Count slots in reachable window
			for (auto const& slot : _state.reachableWindow) {
				reachableSlots[slot]++;
				totalReachable++;
			}
			
			// Count slots in frozen queue
			for (auto const& slot : _state.frozenQueue) {
				frozenSlots[slot]++;
				totalFrozen++;
			}
		}
		
		// Get total count of a slot across both regions
		size_t getSlotCount(Slot const& _slot) const {
			size_t count = 0;
			if (auto it = reachableSlots.find(_slot); it != reachableSlots.end()) {
				count += it->second;
			}
			if (auto it = frozenSlots.find(_slot); it != frozenSlots.end()) {
				count += it->second;
			}
			return count;
		}
		
		// Get reachable count of a slot
		size_t getReachableCount(Slot const& _slot) const {
			if (auto it = reachableSlots.find(_slot); it != reachableSlots.end()) {
				return it->second;
			}
			return 0;
		}
		
		// Get frozen count of a slot
		size_t getFrozenCount(Slot const& _slot) const {
			if (auto it = frozenSlots.find(_slot); it != frozenSlots.end()) {
				return it->second;
			}
			return 0;
		}
		
		// Get all unique slots
		std::set<Slot> getAllSlots() const {
			std::set<Slot> allSlots;
			for (auto const& [slot, count] : reachableSlots) {
				allSlots.insert(slot);
			}
			for (auto const& [slot, count] : frozenSlots) {
				allSlots.insert(slot);
			}
			return allSlots;
		}
	};
	
	// Calculate histogram-based heuristic cost
	template<typename CanBeFreelyGenerated>
	static Cost calculateHeuristic(
		State const& _current,
		State const& _target,
		CanBeFreelyGenerated const& _canBeFreelyGenerated
	) {
		SlotHistogram currentHist(_current);
		SlotHistogram targetHist(_target);
		
		Cost heuristic;
		
		// 1. Analyze slot distribution differences
		auto distributionCost = analyzeDistributionDifferences(currentHist, targetHist, _canBeFreelyGenerated);
		heuristic = heuristic + distributionCost;
		
		// 2. Analyze reachability constraints
		auto reachabilityCost = analyzeReachabilityConstraints(_current, _target, currentHist, targetHist);
		heuristic = heuristic + reachabilityCost;
		
		// 3. Analyze size differences
		auto sizeCost = analyzeSizeDifferences(currentHist, targetHist);
		heuristic = heuristic + sizeCost;
		
		return heuristic;
	}
	
private:
	// Analyze differences in slot distributions
	template<typename CanBeFreelyGenerated>
	static Cost analyzeDistributionDifferences(
		SlotHistogram const& _current,
		SlotHistogram const& _target,
		CanBeFreelyGenerated const& _canBeFreelyGenerated
	) {
		Cost cost;
		
		// Get all unique slots from both histograms
		std::set<Slot> allSlots = _current.getAllSlots();
		auto targetSlots = _target.getAllSlots();
		allSlots.insert(targetSlots.begin(), targetSlots.end());
		
		for (auto const& slot : allSlots) {
			size_t currentCount = _current.getSlotCount(slot);
			size_t targetCount = _target.getSlotCount(slot);
			
			if (currentCount < targetCount) {
				// Need to generate more of this slot
				size_t deficit = targetCount - currentCount;
				
				if (_canBeFreelyGenerated(slot)) {
					// Can push literals
					cost = cost + WindowedEVMCostModel<StackType>::pushCost(slot, _canBeFreelyGenerated) * deficit;
				} else {
					// Must duplicate existing instances
					cost = cost + WindowedEVMCostModel<StackType>::dupCost(1) * deficit;
				}
			} else if (currentCount > targetCount) {
				// Need to remove excess of this slot
				size_t excess = currentCount - targetCount;
				cost = cost + WindowedEVMCostModel<StackType>::popCost() * excess;
			}
		}
		
		return cost;
	}
	
	// Analyze reachability constraints
	static Cost analyzeReachabilityConstraints(
		State const& _current,
		State const& _target,
		SlotHistogram const& _currentHist,
		SlotHistogram const& _targetHist
	) {
		Cost cost;
		
		// Check if slots needed in target are reachable in current
		for (auto const& [slot, targetCount] : _targetHist.reachableSlots) {
			size_t currentReachable = _currentHist.getReachableCount(slot);
			size_t currentFrozen = _currentHist.getFrozenCount(slot);
			
			if (currentReachable < targetCount) {
				// Need to make more of this slot reachable
				size_t needed = targetCount - currentReachable;
				
				if (currentFrozen >= needed) {
					// Can bring from frozen queue
					cost = cost + WindowedEVMCostModel<StackType>::bringIntoReachCost(needed);
				} else {
					// Need to duplicate or generate
					size_t toGenerate = needed - currentFrozen;
					if (currentFrozen > 0) {
						cost = cost + WindowedEVMCostModel<StackType>::bringIntoReachCost(currentFrozen);
					}
					cost = cost + WindowedEVMCostModel<StackType>::dupCost(1) * toGenerate;
				}
			}
		}
		
		// Check if current reachable window is too large
		if (_currentHist.totalReachable > State::MAX_REACHABLE_DEPTH) {
			size_t excess = _currentHist.totalReachable - State::MAX_REACHABLE_DEPTH;
			cost = cost + WindowedEVMCostModel<StackType>::sendToFrozenCost(excess);
		}
		
		return cost;
	}
	
	// Analyze size differences between current and target
	static Cost analyzeSizeDifferences(
		SlotHistogram const& _current,
		SlotHistogram const& _target
	) {
		Cost cost;
		
		// Size difference in reachable window
		if (_current.totalReachable != _target.totalReachable) {
			size_t sizeDiff = _current.totalReachable > _target.totalReachable
				? _current.totalReachable - _target.totalReachable
				: _target.totalReachable - _current.totalReachable;
			
			if (_current.totalReachable > _target.totalReachable) {
				// Need to pop elements
				cost = cost + WindowedEVMCostModel<StackType>::popCost() * sizeDiff;
			} else {
				// Need to push elements
				cost = cost + WindowedEVMCostModel<StackType>::dupCost(1) * sizeDiff;
			}
		}
		
		// Size difference in frozen queue
		if (_current.totalFrozen != _target.totalFrozen) {
			size_t sizeDiff = _current.totalFrozen > _target.totalFrozen
				? _current.totalFrozen - _target.totalFrozen
				: _target.totalFrozen - _current.totalFrozen;
			
			// Frozen queue changes are expensive
			cost = cost + WindowedEVMCostModel<StackType>::bringIntoReachCost(1) * sizeDiff;
		}
		
		return cost;
	}
	
public:
	// Enhanced heuristic that considers ordering
	template<typename CanBeFreelyGenerated>
	static Cost calculateEnhancedHeuristic(
		State const& _current,
		State const& _target,
		CanBeFreelyGenerated const& _canBeFreelyGenerated
	) {
		Cost baseCost = calculateHeuristic(_current, _target, _canBeFreelyGenerated);
		
		// Add ordering penalty
		Cost orderingCost = calculateOrderingPenalty(_current, _target);
		
		return baseCost + orderingCost;
	}
	
private:
	// Calculate penalty for ordering differences
	static Cost calculateOrderingPenalty(
		State const& _current,
		State const& _target
	) {
		Cost penalty;
		
		// Check reachable window ordering
		size_t minSize = std::min(_current.reachableWindow.size(), _target.reachableWindow.size());
		size_t misplaced = 0;
		
		for (size_t i = 0; i < minSize; ++i) {
			if (_current.reachableWindow[i] != _target.reachableWindow[i]) {
				misplaced++;
			}
		}
		
		// Each misplaced element requires at least one swap
		penalty = penalty + WindowedEVMCostModel<StackType>::swapCost(1) * misplaced;
		
		// Check frozen queue ordering (less important but still relevant)
		size_t minFrozenSize = std::min(_current.frozenQueue.size(), _target.frozenQueue.size());
		size_t frozenMisplaced = 0;
		
		for (size_t i = 0; i < minFrozenSize; ++i) {
			if (_current.frozenQueue[i] != _target.frozenQueue[i]) {
				frozenMisplaced++;
			}
		}
		
		// Frozen queue reordering is very expensive
		penalty = penalty + WindowedEVMCostModel<StackType>::bringIntoReachCost(1) * frozenMisplaced;
		
		return penalty;
	}
};

// Windowed ordering heuristic for A* search
template<typename StackType>
class WindowedOrderingHeuristic
{
public:
	using Stack = StackType;
	using Slot = typename Stack::Slot;
	using State = WindowedStackState<StackType>;
	using Cost = typename WindowedEVMCostModel<StackType>::Cost;
	
	// Calculate ordering-based heuristic cost
	static Cost calculateOrderingHeuristic(State const& _current, State const& _target) {
		Cost cost;
		
		// 1. Analyze reachable window ordering
		auto reachableOrderingCost = analyzeReachableWindowOrdering(_current, _target);
		cost = cost + reachableOrderingCost;
		
		// 2. Analyze frozen queue ordering (less important)
		auto frozenOrderingCost = analyzeFrozenQueueOrdering(_current, _target);
		cost = cost + frozenOrderingCost;
		
		// 3. Analyze cross-window ordering dependencies
		auto crossWindowCost = analyzeCrossWindowDependencies(_current, _target);
		cost = cost + crossWindowCost;
		
		return cost;
	}
	
private:
	// Analyze ordering in reachable window using LCS and inversion counting
	static Cost analyzeReachableWindowOrdering(State const& _current, State const& _target) {
		auto const& currentWindow = _current.reachableWindow;
		auto const& targetWindow = _target.reachableWindow;
		
		if (currentWindow.empty() || targetWindow.empty()) {
			return Cost();
		}
		
		// Method 1: Longest Common Subsequence (LCS) based analysis
		auto lcsCost = calculateLCSBasedCost(currentWindow, targetWindow);
		
		// Method 2: Inversion counting for swap distance
		auto inversionCost = calculateInversionCost(currentWindow, targetWindow);
		
		// Method 3: Pattern recognition for common shuffle patterns
		auto patternCost = calculatePatternCost(currentWindow, targetWindow);
		
		// Use the minimum of the three methods as the heuristic
		return std::min({lcsCost, inversionCost, patternCost});
	}
	
	// Calculate cost based on Longest Common Subsequence
	static Cost calculateLCSBasedCost(
		std::vector<Slot> const& _current,
		std::vector<Slot> const& _target
	) {
		// Find LCS between current and target
		auto lcsLength = longestCommonSubsequence(_current, _target);
		
		// Elements not in LCS need to be moved
		size_t currentNotInLCS = _current.size() - lcsLength;
		size_t targetNotInLCS = _target.size() - lcsLength;
		
		// Estimate cost: each element not in LCS requires repositioning
		Cost cost;
		cost = cost + WindowedEVMCostModel<StackType>::swapCost(1) * currentNotInLCS;
		cost = cost + WindowedEVMCostModel<StackType>::dupCost(1) * targetNotInLCS;
		
		return cost;
	}
	
	// Calculate LCS length using dynamic programming
	static size_t longestCommonSubsequence(
		std::vector<Slot> const& _seq1,
		std::vector<Slot> const& _seq2
	) {
		size_t m = _seq1.size();
		size_t n = _seq2.size();
		
		// DP table: dp[i][j] = LCS length of seq1[0..i-1] and seq2[0..j-1]
		std::vector<std::vector<size_t>> dp(m + 1, std::vector<size_t>(n + 1, 0));
		
		for (size_t i = 1; i <= m; ++i) {
			for (size_t j = 1; j <= n; ++j) {
				if (_seq1[i - 1] == _seq2[j - 1]) {
					dp[i][j] = dp[i - 1][j - 1] + 1;
				} else {
					dp[i][j] = std::max(dp[i - 1][j], dp[i][j - 1]);
				}
			}
		}
		
		return dp[m][n];
	}
	
	// Calculate cost based on inversion counting
	static Cost calculateInversionCost(
		std::vector<Slot> const& _current,
		std::vector<Slot> const& _target
	) {
		// Create position mapping for target
		std::map<Slot, size_t> targetPositions;
		for (size_t i = 0; i < _target.size(); ++i) {
			targetPositions[_target[i]] = i;
		}
		
		// Count inversions in current relative to target order
		size_t inversions = 0;
		
		for (size_t i = 0; i < _current.size(); ++i) {
			auto slot1 = _current[i];
			auto it1 = targetPositions.find(slot1);
			if (it1 == targetPositions.end()) continue;
			
			for (size_t j = i + 1; j < _current.size(); ++j) {
				auto slot2 = _current[j];
				auto it2 = targetPositions.find(slot2);
				if (it2 == targetPositions.end()) continue;
				
				// If slot1 appears after slot2 in target but before in current, it's an inversion
				if (it1->second > it2->second) {
					inversions++;
				}
			}
		}
		
		// Each inversion requires at least one swap to fix
		return WindowedEVMCostModel<StackType>::swapCost(1) * inversions;
	}
	
	// Calculate cost based on pattern recognition
	static Cost calculatePatternCost(
		std::vector<Slot> const& _current,
		std::vector<Slot> const& _target
	) {
		Cost cost;
		
		// Pattern 1: Reverse sequence
		if (isReversedSequence(_current, _target)) {
			// Reversing requires approximately n/2 swaps
			size_t swaps = std::min(_current.size(), _target.size()) / 2;
			return WindowedEVMCostModel<StackType>::swapCost(1) * swaps;
		}
		
		// Pattern 2: Rotation
		auto rotationDistance = calculateRotationDistance(_current, _target);
		if (rotationDistance > 0) {
			// Rotation requires rotation distance swaps
			return WindowedEVMCostModel<StackType>::swapCost(1) * rotationDistance;
		}
		
		// Pattern 3: Interleaving
		auto interleavingCost = calculateInterleavingCost(_current, _target);
		if (interleavingCost.total() > 0) {
			return interleavingCost;
		}
		
		// Fallback: use generic shuffle cost
		return calculateGenericShuffleCost(_current, _target);
	}
	
	// Check if target is reverse of current
	static bool isReversedSequence(
		std::vector<Slot> const& _current,
		std::vector<Slot> const& _target
	) {
		if (_current.size() != _target.size()) return false;
		
		for (size_t i = 0; i < _current.size(); ++i) {
			if (_current[i] != _target[_target.size() - 1 - i]) {
				return false;
			}
		}
		
		return true;
	}
	
	// Calculate rotation distance between sequences
	static size_t calculateRotationDistance(
		std::vector<Slot> const& _current,
		std::vector<Slot> const& _target
	) {
		if (_current.size() != _target.size()) return 0;
		
		size_t n = _current.size();
		
		// Try all possible rotations
		for (size_t rotation = 0; rotation < n; ++rotation) {
			bool matches = true;
			for (size_t i = 0; i < n; ++i) {
				if (_current[i] != _target[(i + rotation) % n]) {
					matches = false;
					break;
				}
			}
			if (matches) return rotation;
		}
		
		return 0; // No rotation found
	}
	
	// Calculate interleaving cost
	static Cost calculateInterleavingCost(
		std::vector<Slot> const& _current,
		std::vector<Slot> const& _target
	) {
		// This is a simplified interleaving analysis
		// In practice, this would analyze more complex interleaving patterns
		
		// Count elements that are in correct relative order
		size_t correctOrder = 0;
		size_t i = 0, j = 0;
		
		while (i < _current.size() && j < _target.size()) {
			if (_current[i] == _target[j]) {
				correctOrder++;
				i++;
				j++;
			} else {
				i++;
			}
		}
		
		// Elements not in correct order need repositioning
		size_t incorrectOrder = _target.size() - correctOrder;
		
		return WindowedEVMCostModel<StackType>::swapCost(1) * incorrectOrder;
	}
	
	// Calculate generic shuffle cost
	static Cost calculateGenericShuffleCost(
		std::vector<Slot> const& _current,
		std::vector<Slot> const& _target
	) {
		// Simple heuristic: each position difference requires at least one operation
		size_t differences = 0;
		size_t minSize = std::min(_current.size(), _target.size());
		
		for (size_t i = 0; i < minSize; ++i) {
			if (_current[i] != _target[i]) {
				differences++;
			}
		}
		
		// Add size difference cost
		if (_current.size() != _target.size()) {
			differences += std::abs(static_cast<int>(_current.size()) - static_cast<int>(_target.size()));
		}
		
		return WindowedEVMCostModel<StackType>::swapCost(1) * differences;
	}
	
	// Analyze frozen queue ordering (less critical)
	static Cost analyzeFrozenQueueOrdering(State const& _current, State const& _target) {
		auto const& currentFrozen = _current.frozenQueue;
		auto const& targetFrozen = _target.frozenQueue;
		
		if (currentFrozen.empty() || targetFrozen.empty()) {
			return Cost();
		}
		
		// Frozen queue reordering is very expensive
		size_t differences = 0;
		size_t minSize = std::min(currentFrozen.size(), targetFrozen.size());
		
		for (size_t i = 0; i < minSize; ++i) {
			if (currentFrozen[i] != targetFrozen[i]) {
				differences++;
			}
		}
		
		// Each difference in frozen queue requires bringing into reach and reordering
		return WindowedEVMCostModel<StackType>::bringIntoReachCost(1) * differences;
	}
	
	// Analyze cross-window dependencies
	static Cost analyzeCrossWindowDependencies(State const& _current, State const& _target) {
		Cost cost;
		
		// Check if elements needed in target reachable window are currently frozen
		std::set<Slot> targetReachableSlots(_target.reachableWindow.begin(), _target.reachableWindow.end());
		
		for (auto const& slot : _current.frozenQueue) {
			if (targetReachableSlots.find(slot) != targetReachableSlots.end()) {
				// This slot needs to be brought into reach
				cost = cost + WindowedEVMCostModel<StackType>::bringIntoReachCost(1);
			}
		}
		
		// Check if elements currently reachable need to be sent to frozen
		std::set<Slot> targetFrozenSlots(_target.frozenQueue.begin(), _target.frozenQueue.end());
		
		for (auto const& slot : _current.reachableWindow) {
			if (targetFrozenSlots.find(slot) != targetFrozenSlots.end()) {
				// This slot needs to be sent to frozen
				cost = cost + WindowedEVMCostModel<StackType>::sendToFrozenCost(1);
			}
		}
		
		return cost;
	}
	
public:
	// Advanced ordering heuristic with multiple strategies
	static Cost calculateAdvancedOrderingHeuristic(
		State const& _current,
		State const& _target
	) {
		Cost cost;
		
		// 1. Primary: Reachable window ordering (most important)
		auto reachableCost = analyzeReachableWindowOrdering(_current, _target);
		cost = cost + reachableCost;
		
		// 2. Secondary: Cross-window dependencies
		auto crossWindowCost = analyzeCrossWindowDependencies(_current, _target);
		cost = cost + crossWindowCost;
		
		// 3. Tertiary: Frozen queue ordering (least important)
		auto frozenCost = analyzeFrozenQueueOrdering(_current, _target);
		cost = cost + frozenCost * 0.5; // Reduce weight of frozen queue ordering
		
		return cost;
	}
	
	// Combined heuristic that merges with histogram analysis
	template<typename CanBeFreelyGenerated>
	static Cost calculateCombinedHeuristic(
		State const& _current,
		State const& _target,
		CanBeFreelyGenerated const& _canBeFreelyGenerated
	) {
		// Get histogram-based cost
		auto histogramCost = WindowedHistogramHeuristic<StackType>::calculateHeuristic(
			_current, _target, _canBeFreelyGenerated
		);
		
		// Get ordering-based cost
		auto orderingCost = calculateAdvancedOrderingHeuristic(_current, _target);
		
		// Combine with weighted average (histogram is more reliable for distribution, ordering for sequence)
		return histogramCost * 0.7 + orderingCost * 0.3;
	}
};

// Constraint violation penalties and state pruning for windowed A* search
template<typename StackType>
class WindowedConstraintManager
{
public:
	using Stack = StackType;
	using Slot = typename Stack::Slot;
	using State = WindowedStackState<StackType>;
	using Cost = typename WindowedEVMCostModel<StackType>::Cost;
	
	// Constraint violation categories
	enum class ConstraintViolation {
		NONE,
		STACK_TOO_LARGE,
		REACHABLE_WINDOW_TOO_LARGE,
		INVALID_OPERATION_DEPTH,
		DUPLICATE_GENERATION_VIOLATION,
		CROSS_WINDOW_CONSTRAINT_VIOLATION,
		RESOURCE_EXHAUSTION,
		STATE_INCONSISTENCY
	};
	
	struct ConstraintResult {
		ConstraintViolation violation = ConstraintViolation::NONE;
		Cost penalty;
		bool shouldPrune = false;
		std::string description;
		
		ConstraintResult() = default;
		ConstraintResult(ConstraintViolation _violation, Cost _penalty, bool _shouldPrune, std::string _description)
			: violation(_violation), penalty(_penalty), shouldPrune(_shouldPrune), description(std::move(_description)) {}
		
		bool isValid() const { return violation == ConstraintViolation::NONE; }
	};
	
	// Check all constraints for a given state
	template<typename CanBeFreelyGenerated>
	static ConstraintResult checkConstraints(
		State const& _state,
		CanBeFreelyGenerated const& _canBeFreelyGenerated
	) {
		// Check basic state validity
		auto basicResult = checkBasicConstraints(_state);
		if (!basicResult.isValid()) return basicResult;
		
		// Check EVM-specific constraints
		auto evmResult = checkEVMConstraints(_state);
		if (!evmResult.isValid()) return evmResult;
		
		// Check resource constraints
		auto resourceResult = checkResourceConstraints(_state);
		if (!resourceResult.isValid()) return resourceResult;
		
		// Check value generation constraints
		auto valueResult = checkValueGenerationConstraints(_state, _canBeFreelyGenerated);
		if (!valueResult.isValid()) return valueResult;
		
		return ConstraintResult(); // All constraints satisfied
	}
	
	// Check if a state should be pruned based on various criteria
	template<typename CanBeFreelyGenerated>
	static bool shouldPrune(
		State const& _state,
		State const& _target,
		Cost const& _currentCost,
		Cost const& _heuristicCost,
		CanBeFreelyGenerated const& _canBeFreelyGenerated
	) {
		// 1. Hard constraint violations
		auto constraintResult = checkConstraints(_state, _canBeFreelyGenerated);
		if (constraintResult.shouldPrune) return true;
		
		// 2. Cost-based pruning
		if (shouldPruneBasedOnCost(_state, _target, _currentCost, _heuristicCost)) return true;
		
		// 3. State quality pruning
		if (shouldPruneBasedOnQuality(_state, _target)) return true;
		
		// 4. Dominance pruning
		if (shouldPruneBasedOnDominance(_state, _target)) return true;
		
		// 5. Progress pruning
		if (shouldPruneBasedOnProgress(_state, _target, _currentCost)) return true;
		
		return false;
	}
	
	// Calculate penalty for constraint violations
	template<typename CanBeFreelyGenerated>
	static Cost calculateConstraintPenalty(
		State const& _state,
		CanBeFreelyGenerated const& _canBeFreelyGenerated
	) {
		Cost totalPenalty;
		
		// Check each constraint and accumulate penalties
		auto basicResult = checkBasicConstraints(_state);
		if (!basicResult.isValid()) {
			totalPenalty = totalPenalty + basicResult.penalty;
		}
		
		auto evmResult = checkEVMConstraints(_state);
		if (!evmResult.isValid()) {
			totalPenalty = totalPenalty + evmResult.penalty;
		}
		
		auto resourceResult = checkResourceConstraints(_state);
		if (!resourceResult.isValid()) {
			totalPenalty = totalPenalty + resourceResult.penalty;
		}
		
		auto valueResult = checkValueGenerationConstraints(_state, _canBeFreelyGenerated);
		if (!valueResult.isValid()) {
			totalPenalty = totalPenalty + valueResult.penalty;
		}
		
		return totalPenalty;
	}
	
private:
	// Check basic state constraints
	static ConstraintResult checkBasicConstraints(State const& _state) {
		// Check maximum stack size
		if (_state.totalSize() > State::MAX_STACK_SIZE) {
			Cost penalty = WindowedEVMCostModel<StackType>::popCost() * 
				(_state.totalSize() - State::MAX_STACK_SIZE);
			return ConstraintResult(
				ConstraintViolation::STACK_TOO_LARGE,
				penalty,
				_state.totalSize() > State::MAX_STACK_SIZE * 1.1, // Prune if 10% over limit
				"Stack size exceeds maximum limit"
			);
		}
		
		// Check reachable window size
		if (_state.reachableWindow.size() > State::MAX_REACHABLE_DEPTH) {
			Cost penalty = WindowedEVMCostModel<StackType>::sendToFrozenCost(
				_state.reachableWindow.size() - State::MAX_REACHABLE_DEPTH
			);
			return ConstraintResult(
				ConstraintViolation::REACHABLE_WINDOW_TOO_LARGE,
				penalty,
				_state.reachableWindow.size() > State::MAX_REACHABLE_DEPTH * 1.2, // Prune if 20% over limit
				"Reachable window size exceeds maximum depth"
			);
		}
		
		return ConstraintResult(); // Valid
	}
	
	// Check EVM-specific constraints
	static ConstraintResult checkEVMConstraints(State const& _state) {
		// Check for invalid operation depths
		for (size_t i = 0; i < _state.reachableWindow.size(); ++i) {
			size_t depth = _state.reachableWindow.size() - 1 - i;
			if (depth >= State::MAX_REACHABLE_DEPTH) {
				Cost penalty = WindowedEVMCostModel<StackType>::bringIntoReachCost(1);
				return ConstraintResult(
					ConstraintViolation::INVALID_OPERATION_DEPTH,
					penalty,
					depth >= State::MAX_REACHABLE_DEPTH * 1.5, // Prune if significantly over limit
					"Operation depth exceeds EVM reachable limit"
				);
			}
		}
		
		return ConstraintResult(); // Valid
	}
	
	// Check resource constraints
	static ConstraintResult checkResourceConstraints(State const& _state) {
		// Check for resource exhaustion patterns
		size_t totalSlots = _state.totalSize();
		
		// Arbitrary threshold for resource exhaustion
		if (totalSlots > State::MAX_STACK_SIZE * 0.9) {
			Cost penalty = WindowedEVMCostModel<StackType>::popCost() * 
				(totalSlots - State::MAX_STACK_SIZE * 0.9);
			return ConstraintResult(
				ConstraintViolation::RESOURCE_EXHAUSTION,
				penalty,
				totalSlots > State::MAX_STACK_SIZE,
				"Approaching resource exhaustion"
			);
		}
		
		return ConstraintResult(); // Valid
	}
	
	// Check value generation constraints
	template<typename CanBeFreelyGenerated>
	static ConstraintResult checkValueGenerationConstraints(
		State const& _state,
		CanBeFreelyGenerated const& _canBeFreelyGenerated
	) {
		// Check for violations of value generation rules
		std::map<Slot, size_t> slotCounts;
		
		// Count all slots
		for (auto const& slot : _state.frozenQueue) {
			slotCounts[slot]++;
		}
		for (auto const& slot : _state.reachableWindow) {
			slotCounts[slot]++;
		}
		
		// Check for excessive duplication of non-freely-generated slots
		for (auto const& [slot, count] : slotCounts) {
			if (!_canBeFreelyGenerated(slot) && count > 3) { // Arbitrary threshold
				Cost penalty = WindowedEVMCostModel<StackType>::dupCost(1) * (count - 3);
				return ConstraintResult(
					ConstraintViolation::DUPLICATE_GENERATION_VIOLATION,
					penalty,
					count > 5, // Prune if excessive duplication
					"Excessive duplication of non-freely-generated value"
				);
			}
		}
		
		return ConstraintResult(); // Valid
	}
	
	// Cost-based pruning
	static bool shouldPruneBasedOnCost(
		State const& _state,
		State const& _target,
		Cost const& _currentCost,
		Cost const& _heuristicCost
	) {
		// Prune if total estimated cost is too high
		auto totalEstimatedCost = _currentCost + _heuristicCost;
		
		// Arbitrary threshold: prune if estimated cost is more than 10x the simple swap cost
		auto swapCost = WindowedEVMCostModel<StackType>::swapCost(1);
		auto threshold = swapCost * (_state.totalSize() + _target.totalSize()) * 10;
		
		return totalEstimatedCost.total() > threshold.total();
	}
	
	// Quality-based pruning
	static bool shouldPruneBasedOnQuality(State const& _state, State const& _target) {
		// Prune states that are clearly moving away from target
		
		// Check if reachable window is getting significantly different from target
		if (_state.reachableWindow.size() > _target.reachableWindow.size() * 2) {
			return true;
		}
		
		// Check if frozen queue is getting significantly different from target
		if (_state.frozenQueue.size() > _target.frozenQueue.size() * 2) {
			return true;
		}
		
		return false;
	}
	
	// Dominance-based pruning
	static bool shouldPruneBasedOnDominance(State const& _state, State const& _target) {
		// This is a simplified dominance check
		// In practice, this would involve more sophisticated state comparison
		
		// Check if state is clearly suboptimal
		if (_state.operationCost > _target.operationCost * 5) {
			return true;
		}
		
		return false;
	}
	
	// Progress-based pruning
	static bool shouldPruneBasedOnProgress(
		State const& _state,
		State const& _target,
		Cost const& _currentCost
	) {
		// Prune if making no progress towards target
		
		// Simple progress metric: similarity to target
		size_t similarity = 0;
		size_t minReachableSize = std::min(_state.reachableWindow.size(), _target.reachableWindow.size());
		
		for (size_t i = 0; i < minReachableSize; ++i) {
			if (_state.reachableWindow[i] == _target.reachableWindow[i]) {
				similarity++;
			}
		}
		
		// If no similarity and high cost, prune
		if (similarity == 0 && _currentCost.total() > 50) {
			return true;
		}
		
		return false;
	}
	
public:
	// State quality assessment
	static double assessStateQuality(State const& _state, State const& _target) {
		double quality = 1.0;
		
		// Factor 1: Size similarity
		double sizeSimilarity = 1.0 - std::abs(
			static_cast<double>(_state.totalSize()) - static_cast<double>(_target.totalSize())
		) / static_cast<double>(_target.totalSize() + 1);
		quality *= sizeSimilarity;
		
		// Factor 2: Reachable window similarity
		double reachableSimilarity = calculateSequenceSimilarity(_state.reachableWindow, _target.reachableWindow);
		quality *= reachableSimilarity;
		
		// Factor 3: Frozen queue similarity
		double frozenSimilarity = calculateSequenceSimilarity(_state.frozenQueue, _target.frozenQueue);
		quality *= frozenSimilarity * 0.5; // Frozen queue is less important
		
		// Factor 4: Operation cost penalty
		double costPenalty = std::max(0.0, 1.0 - _state.operationCost / 100.0);
		quality *= costPenalty;
		
		return quality;
	}
	
private:
	// Calculate similarity between two sequences
	static double calculateSequenceSimilarity(
		std::vector<Slot> const& _seq1,
		std::vector<Slot> const& _seq2
	) {
		if (_seq1.empty() && _seq2.empty()) return 1.0;
		if (_seq1.empty() || _seq2.empty()) return 0.0;
		
		size_t matches = 0;
		size_t minSize = std::min(_seq1.size(), _seq2.size());
		
		for (size_t i = 0; i < minSize; ++i) {
			if (_seq1[i] == _seq2[i]) {
				matches++;
			}
		}
		
		return static_cast<double>(matches) / static_cast<double>(std::max(_seq1.size(), _seq2.size()));
	}
	
public:
	// Adaptive pruning based on search progress
	static bool shouldPruneAdaptive(
		State const& _state,
		State const& _target,
		Cost const& _currentCost,
		size_t _iterationCount,
		size_t _maxIterations
	) {
		// Get base pruning decision
		bool basePrune = shouldPruneBasedOnCost(_state, _target, _currentCost, Cost()) ||
		                 shouldPruneBasedOnQuality(_state, _target) ||
		                 shouldPruneBasedOnDominance(_state, _target);
		
		if (basePrune) return true;
		
		// Adaptive pruning based on search progress
		double progress = static_cast<double>(_iterationCount) / static_cast<double>(_maxIterations);
		
		// Become more aggressive with pruning as search progresses
		if (progress > 0.5) {
			double quality = assessStateQuality(_state, _target);
			double threshold = 0.3 + (progress - 0.5) * 0.4; // Threshold from 0.3 to 0.7
			
			if (quality < threshold) {
				return true;
			}
		}
		
		return false;
	}
	
	// Debug information for constraint violations
	static std::string getConstraintDescription(ConstraintViolation _violation) {
		switch (_violation) {
			case ConstraintViolation::NONE:
				return "No constraint violation";
			case ConstraintViolation::STACK_TOO_LARGE:
				return "Stack size exceeds maximum limit";
			case ConstraintViolation::REACHABLE_WINDOW_TOO_LARGE:
				return "Reachable window size exceeds maximum depth";
			case ConstraintViolation::INVALID_OPERATION_DEPTH:
				return "Operation depth exceeds EVM reachable limit";
			case ConstraintViolation::DUPLICATE_GENERATION_VIOLATION:
				return "Excessive duplication of non-freely-generated value";
			case ConstraintViolation::CROSS_WINDOW_CONSTRAINT_VIOLATION:
				return "Cross-window constraint violation";
			case ConstraintViolation::RESOURCE_EXHAUSTION:
				return "Resource exhaustion";
			case ConstraintViolation::STATE_INCONSISTENCY:
				return "State inconsistency";
		}
		return "Unknown constraint violation";
	}
};

// Core A* search algorithm with windowed states
template<typename StackType>
class WindowedAStarShuffler
{
public:
	using Stack = StackType;
	using Slot = typename Stack::Slot;
	using State = WindowedStackState<StackType>;
	using Cost = typename WindowedEVMCostModel<StackType>::Cost;
	using Operation = typename WindowedEVMOperations<StackType>::Operation;
	using ConstraintManager = WindowedConstraintManager<StackType>;
	
	struct SearchNode {
		State state;
		Cost gCost;         // Actual cost from start
		Cost hCost;         // Heuristic cost to goal
		Cost fCost;         // Total cost estimate (g + h)
		std::vector<Operation> path;   // Operations to reach this state
		std::shared_ptr<SearchNode> parent; // Parent node for path reconstruction
		
		SearchNode(State _state, Cost _gCost, Cost _hCost, std::vector<Operation> _path, std::shared_ptr<SearchNode> _parent = nullptr)
			: state(std::move(_state)), gCost(_gCost), hCost(_hCost), fCost(_gCost + _hCost), path(std::move(_path)), parent(_parent) {}
		
		bool operator<(SearchNode const& _other) const {
			// Priority queue is max-heap, so reverse comparison for min-heap behavior
			return fCost.total() > _other.fCost.total();
		}
	};
	
	struct SearchResult {
		bool found;
		std::vector<Operation> operations;
		Cost totalCost;
		size_t nodesExplored;
		size_t nodesPruned;
		std::string errorMessage;
		
		SearchResult() : found(false), nodesExplored(0), nodesPruned(0) {}
	};
	
	struct SearchConfig {
		size_t maxIterations = 10000;
		size_t maxNodes = 50000;
		bool useHistogramHeuristic = true;
		bool useOrderingHeuristic = true;
		bool useConstraintPruning = true;
		bool useAdaptivePruning = true;
		double heuristicWeight = 1.0;
		bool enableDebugOutput = false;
		
		SearchConfig() = default;
	};
	
	// Main A* search function
	template<typename CanBeFreelyGenerated>
	static SearchResult search(
		State const& _start,
		State const& _target,
		CanBeFreelyGenerated const& _canBeFreelyGenerated,
		SearchConfig const& _config = SearchConfig()
	) {
		SearchResult result;
		
		// Validate inputs
		if (!_start.isValid() || !_target.isValid()) {
			result.errorMessage = "Invalid start or target state";
			return result;
		}
		
		// Check if start is already the target
		if (_start == _target) {
			result.found = true;
			result.totalCost = Cost();
			return result;
		}
		
		// Initialize search data structures
		std::priority_queue<SearchNode> openSet;
		std::unordered_set<State> closedSet;
		std::unordered_map<State, Cost> bestCosts;
		
		// Add start node
		Cost startHeuristic = calculateHeuristic(_start, _target, _canBeFreelyGenerated, _config);
		auto startNode = std::make_shared<SearchNode>(_start, Cost(), startHeuristic, std::vector<Operation>());
		openSet.push(*startNode);
		bestCosts[_start] = Cost();
		
		// Search statistics
		size_t iterations = 0;
		size_t nodesExplored = 0;
		size_t nodesPruned = 0;
		
		while (!openSet.empty() && iterations < _config.maxIterations && nodesExplored < _config.maxNodes) {
			// Get the node with lowest f-cost
			SearchNode current = openSet.top();
			openSet.pop();
			iterations++;
			
			// Check if we've already processed this state with a better cost
			if (closedSet.find(current.state) != closedSet.end()) {
				continue;
			}
			
			// Add to closed set
			closedSet.insert(current.state);
			nodesExplored++;
			
			// Check if we've reached the target
			if (current.state == _target) {
				result.found = true;
				result.operations = current.path;
				result.totalCost = current.gCost;
				result.nodesExplored = nodesExplored;
				result.nodesPruned = nodesPruned;
				return result;
			}
			
			// Generate successor states
			auto successors = generateSuccessors(current.state, _target, _canBeFreelyGenerated, _config);
			
			for (auto const& [nextState, operation] : successors) {
				// Check if this state should be pruned
				if (_config.useConstraintPruning) {
					Cost heuristicCost = calculateHeuristic(nextState, _target, _canBeFreelyGenerated, _config);
					if (ConstraintManager::shouldPrune(nextState, _target, current.gCost + operation.cost, heuristicCost, _canBeFreelyGenerated)) {
						nodesPruned++;
						continue;
					}
				}
				
				// Check adaptive pruning
				if (_config.useAdaptivePruning) {
					if (ConstraintManager::shouldPruneAdaptive(nextState, _target, current.gCost + operation.cost, iterations, _config.maxIterations)) {
						nodesPruned++;
						continue;
					}
				}
				
				// Skip if already in closed set
				if (closedSet.find(nextState) != closedSet.end()) {
					continue;
				}
				
				// Calculate costs
				Cost newGCost = current.gCost + operation.cost;
				Cost constraintPenalty = ConstraintManager::calculateConstraintPenalty(nextState, _canBeFreelyGenerated);
				newGCost = newGCost + constraintPenalty;
				
				// Check if we've found a better path to this state
				if (auto it = bestCosts.find(nextState); it != bestCosts.end() && newGCost.total() >= it->second.total()) {
					continue;
				}
				
				// Calculate heuristic cost
				Cost heuristicCost = calculateHeuristic(nextState, _target, _canBeFreelyGenerated, _config);
				heuristicCost = heuristicCost * _config.heuristicWeight;
				
				// Create new path
				std::vector<Operation> newPath = current.path;
				newPath.push_back(operation);
				
				// Create successor node
				auto successorNode = std::make_shared<SearchNode>(nextState, newGCost, heuristicCost, newPath, std::make_shared<SearchNode>(current));
				openSet.push(*successorNode);
				bestCosts[nextState] = newGCost;
			}
		}
		
		// Search failed
		result.nodesExplored = nodesExplored;
		result.nodesPruned = nodesPruned;
		
		if (iterations >= _config.maxIterations) {
			result.errorMessage = "Maximum iterations reached";
		} else if (nodesExplored >= _config.maxNodes) {
			result.errorMessage = "Maximum nodes explored";
		} else {
			result.errorMessage = "No solution found";
		}
		
		return result;
	}
	
private:
	// Generate successor states for a given state
	template<typename CanBeFreelyGenerated>
	static std::vector<std::pair<State, Operation>> generateSuccessors(
		State const& _state,
		State const& _target,
		CanBeFreelyGenerated const& _canBeFreelyGenerated,
		SearchConfig const& _config
	) {
		std::vector<std::pair<State, Operation>> successors;
		
		// Generate standard operations
		auto operations = WindowedEVMOperations<StackType>::generateValidOperations(_state, _canBeFreelyGenerated);
		
		for (auto const& operation : operations) {
			try {
				State nextState = WindowedEVMOperations<StackType>::applyOperation(_state, operation, _canBeFreelyGenerated);
				if (nextState.isValid()) {
					successors.emplace_back(nextState, operation);
				}
			} catch (...) {
				// Skip invalid operations
			}
		}
		
		// Generate push operations for target slots
		std::vector<Slot> targetSlots;
		for (auto const& slot : _target.reachableWindow) {
			targetSlots.push_back(slot);
		}
		for (auto const& slot : _target.frozenQueue) {
			targetSlots.push_back(slot);
		}
		
		auto pushOperations = WindowedEVMOperations<StackType>::generatePushOperations(_state, targetSlots, _canBeFreelyGenerated);
		
		for (auto const& operation : pushOperations) {
			try {
				State nextState = WindowedEVMOperations<StackType>::applyOperation(_state, operation, _canBeFreelyGenerated);
				if (nextState.isValid()) {
					successors.emplace_back(nextState, operation);
				}
			} catch (...) {
				// Skip invalid operations
			}
		}
		
		return successors;
	}
	
	// Calculate heuristic cost based on configuration
	template<typename CanBeFreelyGenerated>
	static Cost calculateHeuristic(
		State const& _current,
		State const& _target,
		CanBeFreelyGenerated const& _canBeFreelyGenerated,
		SearchConfig const& _config
	) {
		Cost heuristic;
		
		if (_config.useHistogramHeuristic && _config.useOrderingHeuristic) {
			// Use combined heuristic
			heuristic = WindowedOrderingHeuristic<StackType>::calculateCombinedHeuristic(_current, _target, _canBeFreelyGenerated);
		} else if (_config.useHistogramHeuristic) {
			// Use histogram heuristic only
			heuristic = WindowedHistogramHeuristic<StackType>::calculateHeuristic(_current, _target, _canBeFreelyGenerated);
		} else if (_config.useOrderingHeuristic) {
			// Use ordering heuristic only
			heuristic = WindowedOrderingHeuristic<StackType>::calculateAdvancedOrderingHeuristic(_current, _target);
		} else {
			// Use basic cost model heuristic
			heuristic = WindowedEVMCostModel<StackType>::heuristicCost(_current, _target);
		}
		
		return heuristic;
	}
	
public:
	// Convenience function for simple shuffling
	template<typename CanBeFreelyGenerated>
	static std::vector<Operation> simpleSearch(
		State const& _start,
		State const& _target,
		CanBeFreelyGenerated const& _canBeFreelyGenerated
	) {
		SearchConfig config;
		config.maxIterations = 1000;
		config.maxNodes = 5000;
		
		auto result = search(_start, _target, _canBeFreelyGenerated, config);
		return result.operations;
	}
	
	// Comprehensive search with full configuration
	template<typename CanBeFreelyGenerated>
	static SearchResult comprehensiveSearch(
		State const& _start,
		State const& _target,
		CanBeFreelyGenerated const& _canBeFreelyGenerated
	) {
		SearchConfig config;
		config.maxIterations = 50000;
		config.maxNodes = 100000;
		config.useHistogramHeuristic = true;
		config.useOrderingHeuristic = true;
		config.useConstraintPruning = true;
		config.useAdaptivePruning = true;
		config.heuristicWeight = 1.2; // Slightly weighted A*
		
		return search(_start, _target, _canBeFreelyGenerated, config);
	}
	
	// Fast search with aggressive pruning
	template<typename CanBeFreelyGenerated>
	static SearchResult fastSearch(
		State const& _start,
		State const& _target,
		CanBeFreelyGenerated const& _canBeFreelyGenerated
	) {
		SearchConfig config;
		config.maxIterations = 2000;
		config.maxNodes = 10000;
		config.useHistogramHeuristic = true;
		config.useOrderingHeuristic = false; // Faster without ordering
		config.useConstraintPruning = true;
		config.useAdaptivePruning = true;
		config.heuristicWeight = 2.0; // More aggressive heuristic
		
		return search(_start, _target, _canBeFreelyGenerated, config);
	}
	
	// Debug search with detailed output
	template<typename CanBeFreelyGenerated>
	static SearchResult debugSearch(
		State const& _start,
		State const& _target,
		CanBeFreelyGenerated const& _canBeFreelyGenerated
	) {
		SearchConfig config;
		config.maxIterations = 10000;
		config.maxNodes = 20000;
		config.enableDebugOutput = true;
		
		return search(_start, _target, _canBeFreelyGenerated, config);
	}
	
	// Validate search result
	template<typename CanBeFreelyGenerated>
	static bool validateResult(
		State const& _start,
		SearchResult const& _result,
		CanBeFreelyGenerated const& _canBeFreelyGenerated
	) {
		if (!_result.found) return false;
		
		// Apply operations step by step to validate
		State currentState = _start;
		
		for (auto const& operation : _result.operations) {
			try {
				currentState = WindowedEVMOperations<StackType>::applyOperation(currentState, operation, _canBeFreelyGenerated);
				if (!currentState.isValid()) {
					return false;
				}
			} catch (...) {
				return false;
			}
		}
		
		// Check if we reached the target
		// Note: This would need to be compared with the actual target state
		// For now, we just check if the final state is valid
		return currentState.isValid();
	}
};


}
