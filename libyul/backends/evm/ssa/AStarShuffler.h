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
#include "range/v3/view/concat.hpp"

#include <libyul/backends/evm/SSACFGStack.h>

#include <queue>
#include <unordered_set>

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
	struct SearchState
	{
		SearchState(std::vector<Slot> const& _tail, std::vector<Slot> const& _head)
		{
			for (auto const& slot: ranges::views::concat(_tail, _head))
			{
				auto const [it, _] = histogram.try_emplace(slot);
				++it->second;
			}
		}
		std::vector<Slot> stackTail{};
		std::vector<Slot> stackHead{};
		std::map<Slot, size_t> histogram;
		size_t cumulativeCost = 0;

		bool operator==(SearchState const& _other) const
		{
			return stackHead == _other.stackHead && histogram == _other.histogram;
		}
	};

	using Cost = size_t;

	void shuffle(SearchState const& _start, SearchState const& _target, size_t _maxIter, size_t _maxNodes)
	{
		// Check if start is already the target
		if (_start == _target) {
			result.found = true;
			result.totalCost = Cost();
			return result;
		}

		// Initialize search data structures
		std::priority_queue<SearchNode> openSet;
		std::unordered_set<SearchState> closedSet;
		std::unordered_map<SearchState, Cost> bestCosts;

		// Add start node
		Cost startHeuristic = calculateHeuristic(_start, _target, _canBeFreelyGenerated, _config);
		auto startNode = std::make_shared<SearchNode>(_start, Cost(), startHeuristic, std::vector<Operation>());
		openSet.push(*startNode);
		bestCosts[_start] = Cost();

		// Search statistics
		size_t iterations = 0;
		size_t nodesExplored = 0;
		size_t nodesPruned = 0;

		while (!openSet.empty() && iterations < _maxIter && nodesExplored < _maxNodes) {
			// Get the node with lowest f-cost
			SearchNode current = openSet.top();
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
				result.found = true;
				result.operations = current.path;
				result.totalCost = current.gCost;
				result.nodesExplored = nodesExplored;
				result.nodesPruned = nodesPruned;
				return result;
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
				auto successorNode = std::make_shared<SearchNode>(nextState, newGCost, heuristicCost, newPath, std::make_shared<SearchNode>(current));
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
