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

#include "libsolidity/parsing/Parser.h"
#include "libyul/backends/evm/SSACFGStackShuffler.h"

#include "libyul/optimiser/SimplificationRules.h"
#include "range/v3/algorithm/equal.hpp"
#include "range/v3/view/concat.hpp"

#include <libyul/backends/evm/SSACFGStack.h>

#include <algorithm>
#include <queue>
#include <unordered_set>
#include <utility>

namespace solidity::yul::ssa
{

template<typename StackType, auto SlotIsCompatible>
class BlockForwardAStarShuffler
{
public:
	using Stack = StackType;
	using Slot = typename StackType::Slot;

private:
	using Cost = size_t;
	struct Operation
	{
		enum class Type
		{
			PUSH, POP, SWAP, DUP, JUNK
		};
		Type type{};
		size_t arg{}; // for swap
		std::optional<Slot> pushValue{};
		Cost cost() const
		{
			return type == Type::JUNK ? 0 : 1;
		}

		void apply(Stack& _stack) const
		{
			switch (type)
			{
			case Type::PUSH:
				yulAssert(pushValue);
				_stack.push(*pushValue);
				break;
			case Type::POP:
				_stack.pop();
				break;
			case Type::SWAP:
				_stack.swap(arg);
				break;
			case Type::DUP:
				yulAssert(pushValue);
				_stack.dup(*pushValue);
				break;
			case Type::JUNK:
				_stack.declareJunk(arg);
				break;
			}
		}
	};

	struct State
	{
		State(typename Stack::Data _stackData, size_t const _numHead):
			stackData(std::move(_stackData)),
			numHead(_numHead)
		{
			for (auto const& slot: stackData)
			{
				auto const [it, _] = histogram.try_emplace(slot);
				++it->second;
			}
		}

		State(State const&) = default;
		State& operator=(State const&) = default;

		size_t numSlot(Slot const& _slot) const
		{
			auto it = histogram.find(_slot);
			if (it == histogram.end())
				return 0;
			return it->second;
		}

		bool operator==(State const& _other) const
		{
			if (_other.stackData.size() != stackData.size())
				return false;

			bool const headEqual = ranges::equal(
				stackData.rbegin(),
				stackData.rbegin() + static_cast<std::ptrdiff_t>(std::min(numHead, stackData.size())),
				_other.stackData.rbegin(),
				_other.stackData.rbegin() + static_cast<std::ptrdiff_t>(std::min(numHead, stackData.size()))
			);
			if (!headEqual)
				return false;

			auto it_a = histogram.begin();
			auto it_b = _other.histogram.begin();

			while (it_a != histogram.end() && it_b != _other.histogram.end())
			{
				if (it_a->first == it_b->first)
				{
					if (it_a->second != it_b->second)
						return false;
					++it_a;
					++it_b;
				} else if (it_a->first < it_b->first)
				{
					if (it_a->second > 0)
						return false;
					++it_a;
				}
				else
				{
					if (it_b->second > 0)
						return false;
					++it_b;
				}
			}

			while (it_a != histogram.end()) {
				if (it_a->second > 0)
					return false;
				++it_a;
			}

			while (it_b != _other.histogram.end()) {
				if (it_b->second > 0)
					return false;
				++it_b;
			}

			return true;
		}

		bool headContains(Slot const& _slot) const
		{
			for (size_t i = 0; i < std::min(stackData.size(), numHead); ++i)
				if (stackData[stackData.size() - i - 1] == _slot)
					return true;
			return false;
		}

		bool operator<(State const& _other) const {
			// 1. Compare stack sizes first
			if (stackData.size() != _other.stackData.size())
				return stackData.size() < _other.stackData.size();

			// 2. Compare heads lexicographically
			size_t const headSize = std::min(numHead, stackData.size());
			size_t const otherHeadSize = std::min(_other.numHead, _other.stackData.size());

			if (headSize != otherHeadSize)
				return headSize < otherHeadSize;

			// Compare head elements
			for (size_t i = 0; i < headSize; ++i) {
				auto thisElem = stackData[stackData.size() - 1 - i];  // Top element
				auto otherElem = _other.stackData[_other.stackData.size() - 1 - i];

				if (thisElem < otherElem) return true;
				if (otherElem < thisElem) return false;
			}

			// 3. If heads identical, compare full histograms (equivalent to tail comparison)
			auto it_a = histogram.begin();
			auto it_b = _other.histogram.begin();

			while (it_a != histogram.end() && it_b != _other.histogram.end())
			{
				if (it_a->first == it_b->first)
				{
					if (it_a->second < it_b->second)
						return true;
					if (it_b->second < it_a->second)
						return false;
					++it_a;
					++it_b;
				}
				else if (it_a->first < it_b->first)
				{
					if (it_a->second > 0)
						return false;
					++it_a;
				}
				else
				{
					if (it_b->second > 0)
						return true;
					++it_b;
				}
			}

			while (it_a != histogram.end()) {
				if (it_a->second > 0)
					return false;
				++it_a;
			}

			while (it_b != _other.histogram.end()) {
				if (it_b->second > 0)
					return true;
				++it_b;
			}

			return false;
		}

		typename Stack::Data stackData;
		size_t numHead;
		std::map<Slot, size_t> histogram;
	};

	struct StatePtrComparator
	{
		bool constexpr operator()(State const* _a, State const* _b) const
		{
			yulAssert(_a);
			yulAssert(_b);
			return *_a < *_b;
		}
	};

	struct Node
	{
		State const* state;
		Cost gCost;
		Cost hCost;
		std::vector<Operation> operations;

		bool operator<(Node const& _other) const
		{
			// we want to get a min-priority queue over nodes
			return gCost + hCost > _other.gCost + _other.hCost;
		}
	};

	static Cost heuristicCost(State const& _from, State const& _to)
	{
		Cost cost{};
		
		// 1. Histogram difference (count constraints)
		auto it_a = _from.histogram.begin();
		auto it_b = _to.histogram.begin();

		while (it_a != _from.histogram.end() && it_b != _to.histogram.end()) {
			if (it_a->first == it_b->first) {
				cost += static_cast<Cost>(std::abs(static_cast<std::ptrdiff_t>(it_a->second) - static_cast<std::ptrdiff_t>(it_b->second)));
				++it_a;
				++it_b;
			} else if (it_a->first < it_b->first) {
				cost += it_a->second;
				++it_a;
			} else {
				cost += it_b->second;
				++it_b;
			}
		}

		while (it_a != _from.histogram.end())
		{
			cost += it_a->second;
			++it_a;
		}

		while (it_b != _to.histogram.end())
		{
			cost += it_b->second;
			++it_b;
		}

		// todo this may be not admissible, check
		// 2. Head accessibility penalty
		/*for (size_t i = 0; i < _to.numHead; ++i) {
			auto targetSlot = _to.stackData[_to.stackData.size() - 1 - i];
			
			// Find the first occurrence of this slot in the current stack
			auto it = std::find(_from.stackData.rbegin(), _from.stackData.rend(), targetSlot);
			if (it != _from.stackData.rend()) {
				size_t depth = static_cast<size_t>(std::distance(_from.stackData.rbegin(), it));
				if (depth >= 16) {
					cost += 1; // Need at least 1 operation to make it accessible
				}
			}
		}*/
		
		return cost;
	}


	static std::vector<std::tuple<State, Operation>> generateSuccessors(State const& _state, State const& _targetState, Stack const& _stack)
	{
		std::vector<std::tuple<State, Operation>> result;
		if (!_state.stackData.empty())
		{
			// Generate SWAP operations - only for bringing needed elements into accessible range
			for (size_t i = 1; i <= std::min(_state.stackData.size() - 1, static_cast<size_t>(16)); ++i)
			{
				if (i < _state.stackData.size()) // Ensure enough elements for SWAPX
				{
					auto const& elementToSwap = _state.stackData[_state.stackData.size() - i - 1];

					// Only generate SWAP if this element is needed in the head
					if (_targetState.headContains(elementToSwap) || (!_targetState.headContains(elementToSwap) && _state.headContains(elementToSwap)))
					{
						result.emplace_back(_state, Operation{Operation::Type::SWAP, i, std::nullopt});
						auto& state = std::get<0>(result.back());
						Stack stack(state.stackData, {}, _stack.canBeFreelyGeneratedFunction());
						stack.swap(i);
					}
				}
			}

			// Generate DUP operations - prioritize deepest accessible elements
			{
				std::vector<std::pair<size_t, Slot>> candidates;
				for (size_t i = 1; i <= std::min(_state.stackData.size(), static_cast<size_t>(16)); ++i)
				{
					if (i <= _state.stackData.size())
					{
						auto const& slotToDup = _state.stackData[_state.stackData.size() - i];
						if (_state.numSlot(slotToDup) < _targetState.numSlot(slotToDup))
						{
							candidates.emplace_back(i, slotToDup);
						}
					}
				}

				// Sort by depth (deepest first) and only generate top 3 DUP operations
				std::sort(candidates.begin(), candidates.end(), [](auto const& a, auto const& b) {
					return a.first > b.first; // Deeper elements first
				});

				size_t const maxDups = std::min(candidates.size(), static_cast<size_t>(2));
				for (size_t j = 0; j < maxDups; ++j)
				{
					auto const& [depth, slotToDup] = candidates[j];
					result.emplace_back(_state, Operation{Operation::Type::DUP, depth, slotToDup});
					State& state = std::get<0>(result.back());
					Stack stack(state.stackData, {}, _stack.canBeFreelyGeneratedFunction());
					stack.dup(slotToDup);
					state.histogram[state.stackData.back()] += 1;
				}
			}

			if (
				_stack.canBeFreelyGenerated(_state.stackData.back()) ||
				_state.numSlot(_state.stackData.back()) > 1 ||
				_targetState.numSlot(_state.stackData.back()) == 0
			)
			{
				result.emplace_back(_state, Operation{Operation::Type::POP});
				State& state = std::get<0>(result.back());
				state.histogram[state.stackData.back()] -= 1;
				state.stackData.pop_back();
			}

			if (_targetState.numSlot(JunkSlot{}) > _state.numSlot(JunkSlot{}))
			{
				size_t n = 0;
				for (size_t i = 0; i < _state.stackData.size(); ++i)
				{
					if (n == 2)
						break;
					// if we have too much of it, we may declare it junk
					if (std::holds_alternative<SSACFG::ValueId>(_state.stackData[i]) && _targetState.numSlot(_state.stackData[i]) < _state.numSlot(_state.stackData[i]))
					{
						result.emplace_back(_state, Operation{Operation::Type::JUNK, _state.stackData.size() - i - 1});
						State& state = std::get<0>(result.back());
						Stack stack(state.stackData, {}, _stack.canBeFreelyGeneratedFunction());
						state.histogram[_state.stackData[i]] -= 1;
						std::get<1>(result.back()).apply(stack);
						state.histogram[JunkSlot{}] += 1;
						++n;
					}
				}
			}
			// todo dup deep slot if needed
		}

		for (auto const& slot: _targetState.stackData)
		{
			if (_stack.canBeFreelyGenerated(slot) && _state.numSlot(slot) < _targetState.numSlot(slot))
			{
				result.emplace_back(_state, Operation{Operation::Type::PUSH, 0, slot});
				State& state = std::get<0>(result.back());
				state.histogram[slot] += 1;
				state.stackData.push_back(slot);
			}
		}
		return result;
	}

	static std::vector<Operation> shuffle(
		std::vector<Slot> const& _initial,
		std::vector<Slot> const& _target,
		size_t const _numHead,
		size_t const _maxIter,
		size_t const _maxNodes,
		Stack const& _inputStack
	)
	{
		yulAssert(_target.size() >= _numHead);
		State const targetState (_target, _numHead);
		State start (_initial, _numHead);
		// Check if start is already the target
		if (start == targetState) {
			return {};
		}

		std::list<State> states;

		// Initialize search data structures
		std::priority_queue<Node> openSet;
		std::set<State const*, StatePtrComparator> closedSet;
		std::map<State const*, Cost, StatePtrComparator> bestCosts;

		// Add start node
		Cost startHeuristic = heuristicCost(start, targetState);
		openSet.push(Node {&start, 0, startHeuristic, {}});
		bestCosts[&start] = {};

		// Search statistics
		size_t iterations = 0;
		size_t nodesExplored = 0;
		// size_t nodesPruned = 0;

		while (!openSet.empty() && iterations < _maxIter && nodesExplored < _maxNodes) {
			// Get the node with lowest f-cost
			Node const current = openSet.top();
			openSet.pop();
			iterations++;

			// Check if we've already processed this state with a better cost
			if (closedSet.contains(current.state)) {
				continue;
			}

			// Add to closed set
			closedSet.insert(current.state);
			nodesExplored++;

			// Check if we've reached the target
			if (*current.state == targetState) {
				return current.operations;
			}

			for (auto const& [nextState, operation]: generateSuccessors(*current.state, targetState, _inputStack))
			{
				// Skip if already in closed set
				if (closedSet.contains(&nextState))
					continue;

				// Calculate costs
				Cost newGCost = current.gCost + operation.cost();

				// Check if we've found a better path to this state
				if (
					auto it = bestCosts.find(&nextState);
					it != bestCosts.end() && newGCost >= it->second
				)
				{
					continue;
				}

				// Calculate heuristic cost
				Cost hCost = heuristicCost(nextState, targetState);

				// Create new path
				std::vector<Operation> newPath = current.operations;
				newPath.push_back(operation);

				// Create successor node
				states.push_back(std::move(nextState));
				auto const* statePtr = &states.back();
				openSet.push(Node{statePtr, newGCost, hCost, newPath});
				bestCosts[statePtr] = newGCost;
			}
		}

		// failed state
		if (iterations >= _maxIter) {
			yulAssert(false, "Maximum iterations reached");
		}
		if (nodesExplored >= _maxNodes) {
			yulAssert(false, "Maximum nodes explored");
		}
		yulAssert(false, "No solution found");
	}
public:
	static void shuffle(Stack& _stack, std::vector<Slot> const& _targetTail, std::vector<Slot> const& _targetHead)
	{
		// Check for common pattern: tail histogram identical, need to build head via DUPs
		if (_stack.data().size() >= _targetTail.size())
		{
			// Compare histograms of current stack and target tail
			std::map<Slot, size_t> currentHistogram, targetHistogram;

			for (size_t i = 0; i < _targetTail.size(); ++i)
				++currentHistogram[_stack.data()[i]];
			for (auto const& slot : _targetTail)
				++targetHistogram[slot];

			if (currentHistogram == targetHistogram)
			{
				DanielShuffler<Stack, SlotIsCompatible>::shuffle(_stack, {}, std::vector(_stack.data().begin(), std::next(_stack.data().begin(), static_cast<std::ptrdiff_t>(_targetTail.size()))) + _targetHead);
				return;
			}
		}

		// Fall back to A* for complex cases
		auto const ops = shuffle(_stack.data(), _targetTail + _targetHead, _targetHead.size(), 100000000, 100000000, _stack);
		for (auto const& op: ops)
			op.apply(_stack);
	}

};
}
