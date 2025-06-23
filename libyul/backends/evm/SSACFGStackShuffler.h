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

#include <range/v3/algorithm/find.hpp>
#include <range/v3/algorithm/find_end.hpp>
#include <range/v3/algorithm/find_if_not.hpp>
#include <range/v3/view/concat.hpp>

#include <concepts>

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

template<typename StackType>
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
				for (auto const x: currentStack)
					++sourceCounts[x];
				for (auto const [i, x]: ranges::views::enumerate(targetStack))
					if (i < currentStack.size() && std::holds_alternative<ssa::JunkSlot>(targetStack[i]))
						++targetCounts[currentStack[i]];
					else
						++targetCounts[x];
			}

			bool isCompatible(size_t _source, size_t _target) const
			{
				return _source < currentStack.size() &&
					_target < targetStack.size() &&
					(
						std::holds_alternative<ssa::JunkSlot>(targetStack[_target]) ||
						currentStack[_source] == targetStack[_target]
					);
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

template<typename StackType>
struct BlockForwardShuffler
{
	using Stack = StackType;
	using SourceSlot = typename Stack::Slot;
	using TargetSlot = typename Stack::Slot;
	static void shuffle(
		Stack& _sourceStack,
		std::set<SourceSlot> const& _operationLiveOutWithoutOutputs,
		std::vector<SourceSlot> const& _requiredStackTop
	)
	{
		struct ShuffleOperations
		{
			size_t const reachableStackDepth = 16;
			Stack& currentStack;
			std::map<SourceSlot, size_t> sourceCounts;
			std::map<TargetSlot, size_t> targetCounts;
			std::vector<SourceSlot> const& targetStackTop;
			std::set<SourceSlot> unassignedLiveOuts;
			std::vector<std::optional<SourceSlot>> liveOutAssignment;

			ShuffleOperations(
				Stack& _currentStack,
				std::vector<SourceSlot> const& _targetStackTop,
				std::set<SourceSlot> const& _operationLiveOutWithoutOutputs
			):
				currentStack(_currentStack),
				targetStackTop(_targetStackTop),
				liveOutAssignment(_operationLiveOutWithoutOutputs.size(), std::nullopt)
			{
				for (auto const x: currentStack)
					++sourceCounts[x];

				for (auto const& slot: ranges::views::concat(_targetStackTop, _operationLiveOutWithoutOutputs))
				{
					yulAssert(!std::holds_alternative<solidity::yul::ssa::JunkSlot>(slot));
					++targetCounts[slot];
				}

				std::set<SourceSlot> usedLiveOuts;
				for (size_t i = 0; i < _operationLiveOutWithoutOutputs.size() && i < currentStack.size(); ++i)
				{
					auto const& currentSlot = currentStack[i];
					if (
						auto it = _operationLiveOutWithoutOutputs.find(currentSlot);
						it != _operationLiveOutWithoutOutputs.end() && !usedLiveOuts.contains(currentSlot)
					)
					{
						liveOutAssignment[i] = currentSlot;
						usedLiveOuts.insert(currentSlot);
					}
				}
				unassignedLiveOuts = _operationLiveOutWithoutOutputs - usedLiveOuts;
			}

			bool isInTargetStackTop(size_t const _targetSlot) const
			{
				return _targetSlot >= liveOutAssignment.size();
			}

			bool isCompatible(size_t _source, size_t _target) const
			{
				if (_source >= currentStack.size() || _target >= liveOutAssignment.size() + targetStackTop.size())
					return false;

				if (isInTargetStackTop(_target))
					return currentStack[_source] == targetStackTop[_target - liveOutAssignment.size()];

				if (liveOutAssignment[_target])
					return *liveOutAssignment[_target] == currentStack[_source];

				// if we are not in the target top, check if there is any other source -> target
				return unassignedLiveOuts.contains(currentStack[_source]);
			}

			bool sourceIsSame(size_t _sourceOffset1, size_t _sourceOffset2) const
			{
				return
					_sourceOffset1 < currentStack.size() &&
					_sourceOffset2 < currentStack.size() &&
					currentStack[_sourceOffset1] == currentStack[_sourceOffset2];
			}

			int sourceMultiplicity(size_t _sourceOffset) const
			{
				auto const& slot = currentStack[_sourceOffset];
				return
					static_cast<int>(solidity::util::valueOrDefault(targetCounts, slot, static_cast<size_t>(0))) -
					static_cast<int>(sourceCounts.at(slot));
			}

			int targetMultiplicity(size_t _targetOffset) const
			{
				if (isInTargetStackTop(_targetOffset))
				{
					auto const& slot = targetStackTop[_targetOffset - liveOutAssignment.size()];
					return
						static_cast<int>(targetCounts.at(slot)) -
						static_cast<int>(solidity::util::valueOrDefault(sourceCounts, slot, static_cast<size_t>(0)));
				}

				if (liveOutAssignment[_targetOffset])
				{
					auto const& slot = *liveOutAssignment[_targetOffset];
					return
						static_cast<int>(targetCounts.at(slot)) -
						static_cast<int>(solidity::util::valueOrDefault(sourceCounts, slot, static_cast<size_t>(0)));
				}

				// we have an unassigned target offset, let's find the max multiplicity of the unassigned
				int max = 0;
				for (auto const& slot: unassignedLiveOuts)
					max = std::max(max, static_cast<int>(targetCounts.at(slot)) - static_cast<int>(solidity::util::valueOrDefault(sourceCounts, slot, static_cast<size_t>(0))));
				return max;
			}

			bool targetIsArbitrary(size_t _targetOffset) const
			{
				if (_targetOffset >= targetSize())
					return false;

				if (isInTargetStackTop(_targetOffset))
					return std::holds_alternative<solidity::yul::ssa::JunkSlot>(targetStackTop[_targetOffset - liveOutAssignment.size()]);

				// no junk in live out tail
				return false;
			}

			size_t sourceSize() const { return currentStack.size(); }
			size_t targetSize() const { return targetStackTop.size() + liveOutAssignment.size(); }

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
				if (isInTargetStackTop(_targetOffset))
				{
					auto const& slot = targetStackTop[_targetOffset - liveOutAssignment.size()];
					currentStack.pushOrDup(slot);
					return;
				}

				if (liveOutAssignment[_targetOffset])
				{
					auto const& slot = *liveOutAssignment[_targetOffset];
					currentStack.pushOrDup(slot);
					return;
				}

				// we have an unassigned target offset, let's find the max multiplicity of the unassigned
				int max = 0;
				std::optional<SourceSlot> maxSlot = std::nullopt;
				for (auto const& slot: unassignedLiveOuts)
				{
					auto delta = static_cast<int>(targetCounts.at(slot)) - static_cast<int>(solidity::util::valueOrDefault(sourceCounts, slot, static_cast<size_t>(0)));
					if (delta > max)
					{
						max = std::max(max, delta);
						maxSlot = slot;
					}
				}
				yulAssert(maxSlot);
				currentStack.pushOrDup(*maxSlot);
			}
		};

		Shuffler<ShuffleOperations>::shuffle(_sourceStack, _requiredStackTop, _operationLiveOutWithoutOutputs);
	}
};

template<typename StackType>
struct BlockStackInShuffler
{
	using Stack = StackType;
	using StackSlot = typename Stack::Slot;
	static Stack shuffle(Stack const& _sourceStack, std::set<StackSlot> const& _liveIn)
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

}
