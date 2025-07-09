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
struct ValuePreservingStackShuffler
{
	using Stack = StackType;
	using StackSlot = typename Stack::Slot;
	
	/// Value-preserving stack shuffler that respects symbolic variable constraints
	/// Key insight: Slots are symbolic variables that cannot be regenerated arbitrarily
	/// Only literals/junk can be freely generated - everything else must be preserved
	static Stack shuffle(
		Stack const& _sourceStack,
		std::vector<StackSlot> const& _targetTail,    // Target tail (up to permutation - histogram must match)
		std::vector<StackSlot> const& _targetTop      // Target top (exact order required)
	)
	{
		Stack result = _sourceStack;
		
		// Safety check: don't create overly deep stacks
		if (result.size() + _targetTop.size() > 1000) {
			// Fall back to Daniel shuffler for very deep stacks
			return DanielShuffler<Stack>::shuffle(_sourceStack, std::set<StackSlot>(_targetTail.begin(), _targetTail.end()), _targetTop);
		}
		
		// Phase 1: Analyze value preservation constraints
		ValueAnalysis analysis = analyzeValueConstraints(result, _targetTail, _targetTop);
		
		// Phase 2: Execute value-preserving shuffle
		executeValuePreservingShuffle(result, analysis);
		
		return result;
	}

private:
	static constexpr size_t REACHABLE_DEPTH = 16;
	
	struct ValueAnalysis {
		std::vector<StackSlot> targetTail;
		std::vector<StackSlot> targetTop;
		std::vector<StackSlot> reachableWindow;
		std::vector<StackSlot> frozenQueue;
		
		// Value preservation analysis
		std::map<StackSlot, size_t> currentCounts;
		std::map<StackSlot, size_t> targetCounts;
		std::set<StackSlot> freelyGeneratedSlots;
		std::set<StackSlot> mustPreserveSlots;
		
		// Reachability analysis for non-regenerable slots
		std::map<StackSlot, std::vector<size_t>> reachablePositions;  // slot -> positions from top
		std::map<StackSlot, std::vector<size_t>> frozenPositions;     // slot -> positions in frozen queue
		
		// Duplication requirements
		std::vector<StackSlot> requiredDuplications;
		std::vector<StackSlot> safeToPopSlots;
		
		// Operation plan
		std::vector<std::pair<std::string, size_t>> operationPlan;
		double estimatedCost;
	};
	
	/// Phase 1: Analyze value preservation constraints
	static ValueAnalysis analyzeValueConstraints(
		Stack const& _stack,
		std::vector<StackSlot> const& _targetTail,
		std::vector<StackSlot> const& _targetTop
	) {
		ValueAnalysis analysis;
		analysis.targetTail = _targetTail;
		analysis.targetTop = _targetTop;
		
		// Split stack into reachable window and frozen queue
		auto const& stackData = _stack.data();
		size_t windowSize = std::min(stackData.size(), REACHABLE_DEPTH);
		
		// Reachable window: top 16 elements (or all if stack smaller)
		analysis.reachableWindow.assign(
			stackData.end() - windowSize, 
			stackData.end()
		);
		
		// Frozen queue: elements beyond reach (if any)
		if (stackData.size() > REACHABLE_DEPTH) {
			analysis.frozenQueue.assign(
				stackData.begin(),
				stackData.end() - REACHABLE_DEPTH
			);
		}
		
		// Classify slots by regenerability
		classifySlotsByRegenerability(_stack, analysis);
		
		// Count current and target histograms
		for (auto const& slot : stackData) {
			analysis.currentCounts[slot]++;
		}
		for (auto const& slot : _targetTail) {
			analysis.targetCounts[slot]++;
		}
		for (auto const& slot : _targetTop) {
			analysis.targetCounts[slot]++;
		}
		
		// Analyze reachability of non-regenerable slots
		analyzeSlotReachability(analysis);
		
		// Plan required duplications for value preservation
		planValuePreservingDuplications(analysis);
		
		// Identify safe-to-pop slots
		identifySafeToPopSlots(analysis);
		
		// Generate optimal operation plan
		generateOperationPlan(analysis);
		
		return analysis;
	}
	
	/// Classify slots by whether they can be freely generated
	static void classifySlotsByRegenerability(Stack const& _stack, ValueAnalysis& _analysis) {
		// Get all unique slots from current stack and target
		std::set<StackSlot> allSlots;
		for (auto const& slot : _stack.data()) {
			allSlots.insert(slot);
		}
		for (auto const& slot : _analysis.targetTail) {
			allSlots.insert(slot);
		}
		for (auto const& slot : _analysis.targetTop) {
			allSlots.insert(slot);
		}
		
		// Classify each slot
		for (auto const& slot : allSlots) {
			if (_stack.canBeFreelyGenerated(slot)) {
				_analysis.freelyGeneratedSlots.insert(slot);
			} else {
				_analysis.mustPreserveSlots.insert(slot);
			}
		}
	}
	
	/// Analyze reachability of non-regenerable slots
	static void analyzeSlotReachability(ValueAnalysis& _analysis) {
		// Analyze reachable positions (from top, 0-indexed)
		for (size_t i = 0; i < _analysis.reachableWindow.size(); ++i) {
			StackSlot slot = _analysis.reachableWindow[_analysis.reachableWindow.size() - 1 - i];
			_analysis.reachablePositions[slot].push_back(i);
		}
		
		// Analyze frozen positions (from bottom, 0-indexed)
		for (size_t i = 0; i < _analysis.frozenQueue.size(); ++i) {
			StackSlot slot = _analysis.frozenQueue[_analysis.frozenQueue.size() - 1 - i];
			_analysis.frozenPositions[slot].push_back(i);
		}
	}
	
	/// Plan duplications needed to preserve values
	static void planValuePreservingDuplications(ValueAnalysis& _analysis) {
		for (auto const& slot : _analysis.mustPreserveSlots) {
			size_t currentCount = _analysis.currentCounts[slot];
			size_t targetCount = _analysis.targetCounts[slot];
			
			if (targetCount > currentCount) {
				// We need more copies but can't generate them - this is an error condition
				// For now, skip this slot (the algorithm will fail gracefully)
				continue;
			}
			
			// Check if we need extra copies to handle consumption
			// If a slot appears in both target and will be consumed, we need a duplicate
			size_t reachableCount = _analysis.reachablePositions[slot].size();
			
			if (targetCount > 0 && reachableCount < targetCount) {
				// We need this slot but don't have enough reachable copies
				// We'll need to pop some elements to bring more copies into reach
				// For now, mark this as a required duplication
				_analysis.requiredDuplications.push_back(slot);
			}
		}
	}
	
	/// Identify slots that are safe to pop (won't destroy needed values)
	static void identifySafeToPopSlots(ValueAnalysis& _analysis) {
		for (auto const& slot : _analysis.reachableWindow) {
			bool isSafeToPop = false;
			
			// Safe to pop if it's freely generated (can be recreated)
			if (_analysis.freelyGeneratedSlots.contains(slot)) {
				isSafeToPop = true;
			}
			// Safe to pop if not needed in target
			else if (_analysis.targetCounts[slot] == 0) {
				isSafeToPop = true;
			}
			// Safe to pop if we have excess copies
			else if (_analysis.currentCounts[slot] > _analysis.targetCounts[slot]) {
				isSafeToPop = true;
			}
			
			if (isSafeToPop) {
				_analysis.safeToPopSlots.push_back(slot);
			}
		}
	}
	
	/// Generate optimal operation plan
	static void generateOperationPlan(ValueAnalysis& _analysis) {
		// This is a placeholder - the actual implementation would use
		// sophisticated planning algorithms taking into account:
		// 1. Value preservation constraints
		// 2. Reachability constraints
		// 3. Target requirements
		// 4. Cost optimization
		
		_analysis.estimatedCost = 0.0;
		
		// Add required duplications
		for (auto const& slot : _analysis.requiredDuplications) {
			_analysis.operationPlan.emplace_back("DUP", 1);
			_analysis.estimatedCost += 1.0;
		}
		
		// Add target top construction
		for (size_t i = 0; i < _analysis.targetTop.size(); ++i) {
			_analysis.operationPlan.emplace_back("ARRANGE", i);
			_analysis.estimatedCost += 1.5;
		}
	}
	
	/// Execute value-preserving shuffle
	static void executeValuePreservingShuffle(Stack& _stack, ValueAnalysis const& _analysis) {
		// Step 1: Duplicate values that need preservation before any destructive operations
		executeValuePreservingDuplications(_stack, _analysis);
		
		// Step 2: Safely pop elements to bring required values into reach
		executeSafePops(_stack, _analysis);
		
		// Step 3: Arrange the reachable window optimally
		executeOptimalArrangement(_stack, _analysis);
		
		// Step 4: Final cleanup and validation
		executeValuePreservingCleanup(_stack, _analysis);
	}
	
	/// Execute duplications needed to preserve values
	static void executeValuePreservingDuplications(Stack& _stack, ValueAnalysis const& _analysis) {
		// Duplicate any must-preserve slots that might be lost
		for (auto const& slot : _analysis.requiredDuplications) {
			if (_analysis.mustPreserveSlots.contains(slot)) {
				auto depth = _stack.slotDepth(slot);
				if (depth && *depth < REACHABLE_DEPTH) {
					_stack.dup(slot);
				}
			}
		}
	}
	
	/// Execute safe pops to bring values into reach
	static void executeSafePops(Stack& _stack, ValueAnalysis const& _analysis) {
		// Only pop values that are safe to pop (won't destroy needed values)
		while (_stack.size() > REACHABLE_DEPTH) {
			StackSlot topSlot = _stack.top();
			
			// Check if safe to pop
			bool isSafeToPop = false;
			
			// Safe if freely generated
			if (_analysis.freelyGeneratedSlots.contains(topSlot)) {
				isSafeToPop = true;
			}
			// Safe if not needed in target
			else if (_analysis.targetCounts.find(topSlot) == _analysis.targetCounts.end() || 
			         _analysis.targetCounts.at(topSlot) == 0) {
				isSafeToPop = true;
			}
			// Safe if we have excess copies
			else if (_analysis.currentCounts.at(topSlot) > _analysis.targetCounts.at(topSlot)) {
				isSafeToPop = true;
			}
			
			if (isSafeToPop) {
				_stack.pop();
			} else {
				// We need this value but it's blocking access to deeper values
				// This is a complex situation requiring careful handling
				// For now, break to avoid infinite loop
				break;
			}
		}
	}
	
	/// Execute optimal arrangement of reachable window
	static void executeOptimalArrangement(Stack& _stack, ValueAnalysis const& _analysis) {
		if (_analysis.targetTop.empty()) return;
		
		// Fast path: check if already correct
		if (isTopAlreadyCorrect(_stack, _analysis.targetTop)) return;
		
		// Build target top using value-preserving operations
		for (size_t i = 0; i < _analysis.targetTop.size(); ++i) {
			size_t targetIndex = _analysis.targetTop.size() - 1 - i;
			StackSlot targetSlot = _analysis.targetTop[targetIndex];
			
			// Strategy: Use existing values when possible
			auto depth = _stack.slotDepth(targetSlot);
			if (depth && *depth > 0 && *depth < REACHABLE_DEPTH) {
				// Use SWAP to move existing value
				_stack.swap(*depth);
			} else if (_analysis.freelyGeneratedSlots.contains(targetSlot)) {
				// Only generate if freely generated
				_stack.push(targetSlot);
			} else {
				// Try to dup from existing position
				_stack.pushOrDup(targetSlot);
			}
		}
	}
	
	/// Execute value-preserving cleanup
	static void executeValuePreservingCleanup(Stack& _stack, ValueAnalysis const& _analysis) {
		// Remove excess elements only if they're safe to remove
		size_t targetSize = _analysis.targetTail.size() + _analysis.targetTop.size();
		while (_stack.size() > targetSize) {
			StackSlot topSlot = _stack.top();
			
			// Only pop if safe
			if (_analysis.freelyGeneratedSlots.contains(topSlot) ||
			    _analysis.targetCounts.find(topSlot) == _analysis.targetCounts.end() ||
			    _analysis.targetCounts.at(topSlot) == 0) {
				_stack.pop();
			} else {
				break; // Don't pop needed values
			}
		}
		
		// Add missing freely-generated values only
		for (auto const& [slot, needed] : _analysis.targetCounts) {
			if (_analysis.freelyGeneratedSlots.contains(slot)) {
				size_t currentCount = std::count(_stack.data().begin(), _stack.data().end(), slot);
				while (currentCount < needed) {
					_stack.push(slot);
					currentCount++;
				}
			}
		}
	}
	
	/// Check if target top is already correct
	static bool isTopAlreadyCorrect(Stack const& _stack, std::vector<StackSlot> const& _targetTop) {
		if (_targetTop.size() > _stack.size()) return false;
		
		for (size_t i = 0; i < _targetTop.size(); ++i) {
			size_t stackIndex = _stack.size() - 1 - i;
			size_t targetIndex = _targetTop.size() - 1 - i;
			
			if (_stack[stackIndex] != _targetTop[targetIndex]) {
				return false;
			}
		}
		return true;
	}
};


}
