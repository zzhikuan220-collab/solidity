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

#include <libyul/backends/evm/SSACFGLoopNestingForest.h>
#include <libyul/backends/evm/SSACFGTopologicalSort.h>
#include <libyul/backends/evm/SSAControlFlowGraph.h>

#include <range/v3/algorithm/find_if.hpp>

#include <set>
#include <vector>

namespace solidity::yul
{

/// Performs liveness analysis on a reducible SSA CFG following Algorithm 9.1 in [1].
///
/// [1] Rastello, Fabrice, and Florent Bouchez Tichadou, eds. SSA-based Compiler Design. Springer, 2022.
class SSACFGLiveness
{
public:
	class LivenessData
	{
	public:
		using Count = std::uint32_t;
		using Value = SSACFG::ValueId;
		using LiveCounts = std::vector<std::pair<Value, Count>>;

		LivenessData() = default;
		template<std::input_iterator Iter, std::sentinel_for<Iter> Sentinel>
		LivenessData(Iter begin, Sentinel end): liveCounts(begin, end) {}

		bool contains(SSACFG::ValueId const& _valueId) const;
		Count count(SSACFG::ValueId const& _valueId) const;
		LiveCounts::const_iterator begin() const;
		LiveCounts::const_iterator end() const;
		LiveCounts::size_type size() const;
		bool empty() const;

		// Core modification
		/// Add value with count (default 1), incrementing if already present
		void insert(Value const& _value, Count _count = 1);
		/// Remove value completely regardless of count
		void erase(Value const& _value);
		/// Decrement value count, removing if count reaches zero
		void remove(Value const& _value, Count _count = 1);

		// Set operations
		/// Add all entries from other, summing counts
		LivenessData& operator+=(LivenessData const& _other);
		/// Remove all values present in other
		LivenessData& operator-=(LivenessData const& _other);
		/// Union with other, taking max count for each value
		LivenessData& maxUnion(LivenessData const& _other);

		// Bulk operations
		/// Insert all values from range with count 1 each
		template<typename Range>
		void insertAll(Range const& _values)
		{
			for (auto const& value : _values)
				insert(value);
		}

		/// Erase all values from range
		template<typename Range>
		void eraseAll(Range const& _values)
		{
			for (auto const& value : _values)
				erase(value);
		}

		// Conditional removal
		/// Remove all entries matching predicate
		template<typename Predicate>
		void eraseIf(Predicate&& _predicate)
		{
			std::erase_if(liveCounts, std::forward<Predicate>(_predicate));
		}

	private:
		auto findEntry(Value const& _value)
		{
			return ranges::find_if(liveCounts, [&](auto const& _entry) { return _entry.first == _value; });
		}

		/// Usage counts represent the total number of times each variable will be used
		/// downstream across all possible execution paths from this program point.
		LiveCounts liveCounts;
	};
	// using OperationLivenessData = std::set<LiveValue>;
	explicit SSACFGLiveness(SSACFG const& _cfg);

	LivenessData const& liveIn(SSACFG::BlockId const _blockId) const { return m_liveIns[_blockId.value]; }
	LivenessData const& liveOut(SSACFG::BlockId const _blockId) const { return m_liveOuts[_blockId.value]; }
	std::vector<LivenessData> const& operationsLiveOut(SSACFG::BlockId _blockId) const { return m_operationLiveOuts[_blockId.value]; }
	ForwardSSACFGTopologicalSort const& topologicalSort() const { return m_topologicalSort; }
	SSACFG const& cfg() const { return m_cfg; }

private:
	void runDagDfs();
	void runLoopTreeDfs(std::size_t _loopHeader);
	void fillOperationsLiveOut();
	LivenessData blockExitValues(SSACFG::BlockId const& _blockId) const;

	SSACFG const& m_cfg;
	ForwardSSACFGTopologicalSort m_topologicalSort;
	SSACFGLoopNestingForest m_loopNestingForest;
	std::vector<LivenessData> m_liveIns;
	std::vector<LivenessData> m_liveOuts;
	std::vector<std::vector<LivenessData>> m_operationLiveOuts;
};

}
