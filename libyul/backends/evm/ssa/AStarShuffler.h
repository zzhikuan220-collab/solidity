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

template<auto SlotIsCompatible>
class BlockForwardAStarShuffler
{
public:
	using Stack = Stack<StackSlot>;
	using Slot = Stack::Slot;

	void shuffle(Stack& _stack, std::vector<Slot> const& _targetTail, std::vector<Slot> const& _targetHead)
	{

	}


private:
	using Cost = size_t;

	struct State
	{
		State(Stack::Data _stackData, size_t const _numHead): stackData(std::move(_stackData)), numHead(_numHead)
		{
			for (auto const& slot: stackData)
			{
				auto const [it, _] = histogram.try_emplace(slot);
				++it->second;
			}
		}
		Stack::Data stackData;
		size_t numHead;
		std::map<Slot, size_t> histogram;
		size_t cumulativeCost = 0;

		bool operator==(State const& _other) const
		{
			if (_other.stack.size() != stack.size())
				return false;

			bool const headEqual = ranges::equal(
				stack.data().rbegin(),
				stack.data().rbegin() + std::min(numHead, stack.size()),
				_other.stack.data().rbegin()
			);
			return headEqual && histogram == _other.histogram;
		}
	};

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
			// todo maybe non-uniform
			return 1;
		}

		void apply(Stack& _stack) const
		{
			// todo
			_stack.pop();
		}
	};

	struct Node
	{
		State state;
		Cost costFromStart{};
		Cost heuristicCost{};
		std::vector<Operation> path;
	};

	std::vector<Operation> shuffle(Stack const& _stack, State const& _target, size_t const _maxIter, size_t const _maxNodes)
	{
		// todo split into head and tail
		State const start ({}, _stack.data());
		// Check if start is already the target
		if (start == _target) {
			return {};
		}

		// Initialize search data structures
		std::priority_queue<Node> openSet;
		std::unordered_set<State> closedSet;
		std::unordered_map<State, Cost> bestCosts;

		// Add start node
		Cost startHeuristic = 0; // calculateHeuristic(_start, _target, _canBeFreelyGenerated, _config);
		auto startNode = std::make_shared<Node>(start, Cost(), startHeuristic, std::vector<Operation>());
		openSet.push(*startNode);
		bestCosts[start] = {};

		// Search statistics
		size_t iterations = 0;
		size_t nodesExplored = 0;
		size_t nodesPruned = 0;

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
			closedSet.insert(current.state);
			nodesExplored++;

			// Check if we've reached the target
			if (current.state == _target) {
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
				Cost heuristicCost = calculateHeuristic(nextState, _target, _canBeFreelyGenerated, _config);
				heuristicCost = heuristicCost; //  * _config.heuristicWeight

				// Create new path
				std::vector<Operation> newPath = current.path;
				newPath.push_back(operation);

				// Create successor node
				auto successorNode = std::make_shared<Node>(nextState, newGCost, heuristicCost, newPath, std::make_shared<Node>(current));
				openSet.push(*successorNode);
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
