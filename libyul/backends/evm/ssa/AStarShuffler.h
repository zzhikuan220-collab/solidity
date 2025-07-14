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

#include "libyul/optimiser/SimplificationRules.h"
#include "range/v3/algorithm/equal.hpp"
#include "range/v3/view/concat.hpp"

#include <libyul/backends/evm/SSACFGStack.h>

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

	void shuffle(Stack& _stack, std::vector<Slot> const& _targetTail, std::vector<Slot> const& _targetHead)
	{

	}


private:
	using Cost = size_t;

	struct Operation
	{
		enum class Type
		{
			PUSH, POP, SWAP, DUP
		};
		Type type;
		size_t arg{}; // for dup and swap
		std::unique_ptr<u256> pushValue{};
		Cost cost() const
		{
			return 1;
		}

		void apply(Stack& _stack) const
		{
			// todo
			_stack.pop();
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

		bool operator==(State const& _other) const
		{
			if (_other.stackData.size() != stackData.size())
				return false;

			bool const headEqual = ranges::equal(
				stackData.rbegin(),
				stackData.rbegin() + std::min(numHead, stackData.size()),
				_other.stackData.rbegin()
			);
			return headEqual && histogram == _other.histogram;
		}

		bool operator<(State const& _other) const
		{
			if (ranges::less{}(
					stackData.rbegin(),
					stackData.rbegin() + std::min(numHead, stackData.size()),
					_other.stackData.rbegin()))
				return true;
			if (ranges::less{}(
					_other.stackData.rbegin(),
					_other.stackData.rbegin() + std::min(_other.numHead, _other.stackData.size()),
					stackData.rbegin()))
				return false;

			return histogram < _other.histogram;
		}

		typename Stack::Data stackData;
		size_t numHead;
		std::map<Slot, size_t> histogram;
		size_t cumulativeCost = 0;
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

	static Cost heuristicCost(std::map<Slot, size_t> const& _from, std::map<Slot, size_t> const& _to)
	{
		Cost cost{};
		auto it_a = _from.begin();
		auto it_b = _to.begin();

		while (it_a != _from.end() && it_b != _to.end()) {
			if (it_a->first == it_b->first) {
				cost += std::abs(static_cast<std::ptrdiff_t>(it_a->second) - static_cast<std::ptrdiff_t>(it_b->second));
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

		while (it_a != _from.end()) {
			cost += it_a->second;
			++it_a;
		}

		while (it_b != _to.end()) {
			cost += it_b->second;
			++it_b;
		}
		return cost;
	}

	static std::vector<Operation> shuffle(
		std::vector<Slot> const& _initial,
		std::vector<Slot> const& _target,
		size_t const _numHead,
		size_t const _maxIter,
		size_t const _maxNodes
	)
	{
		yulAssert(_target.size() >= _numHead);
		State const targetState (_target, _numHead);
		// todo this isn't optimal
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
		Cost startHeuristic = heuristicCost(start.histogram, targetState.histogram);
		openSet.push(Node {&start, 0, startHeuristic, {}});
		bestCosts[start] = {};

		// Search statistics
		size_t iterations = 0;
		size_t nodesExplored = 0;
		// size_t nodesPruned = 0;

		while (!openSet.empty() && iterations < _maxIter && nodesExplored < _maxNodes) {
			// Get the node with lowest f-cost
			Node current = openSet.top();
			openSet.pop();
			iterations++;

			// Check if we've already processed this state with a better cost
			if (closedSet.contains(current.state)) {
				continue;
			}

			// Add to closed set
			closedSet.insert(current);
			nodesExplored++;

			// Check if we've reached the target
			if (current == _target) {
				return current.path;
			}

			// Generate successor states
			auto successors = generateSuccessors(current.state, _target, _canBeFreelyGenerated, _config);

			for (auto const& [nextState, operation]: successors)
			{
				// Check if this state should be pruned
				/*if (_config.useConstraintPruning) {
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
				}*/

				// Skip if already in closed set
				if (closedSet.contains(nextState))
				{
					continue;
				}

				// Calculate costs
				Cost newGCost = current.gCost + operation.cost;
				// Cost constraintPenalty = ConstraintManager::calculateConstraintPenalty(nextState, _canBeFreelyGenerated);
				newGCost = newGCost; //  + constraintPenalty

				// Check if we've found a better path to this state
				if (
					auto it = bestCosts.find(nextState);
					it != bestCosts.end() && newGCost >= it->second.total()
				)
				{
					continue;
				}

				// Calculate heuristic cost
				Cost heuristicCost = calculateHeuristic(nextState.histogram, targetState.histogram);

				// Create new path
				std::vector<Operation> newPath = current.path;
				newPath.push_back(operation);

				// Create successor node
				states.push_back(std::move(nextState));
				auto const* statePtr = states.back();
				openSet.push(Node{statePtr, newGCost, heuristicCost, newPath});
				bestCosts[nextState] = newGCost;
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
};
}
