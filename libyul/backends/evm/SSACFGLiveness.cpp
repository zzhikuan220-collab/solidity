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

#include "range/v3/algorithm/find.hpp"
#include "range/v3/view/enumerate.hpp"


#include <libyul/backends/evm/SSACFGLiveness.h>

#include <libsolutil/Visitor.h>

#include <range/v3/algorithm/set_algorithm.hpp>
#include <range/v3/range/conversion.hpp>
#include <range/v3/view/filter.hpp>
#include <range/v3/view/reverse.hpp>

using namespace solidity::yul;

namespace
{
constexpr auto literalsFilter(SSACFG const& _cfg)
{
	return [&_cfg](SSACFG::ValueId const& _valueId) -> bool
	{
		return !std::holds_alternative<SSACFG::LiteralValue>(_cfg.valueInfo(_valueId));
	};
}
constexpr auto unreachableFilter(SSACFG const& _cfg)
{
	return [&_cfg](SSACFG::ValueId const& _valueId) -> bool
	{
		return !std::holds_alternative<SSACFG::UnreachableValue>(_cfg.valueInfo(_valueId));
	};
}
}

bool SSACFGLiveness::LivenessData::contains(SSACFG::ValueId const& _valueId) const
{
	return ranges::find_if(liveCounts, [&](auto const& entry) { return entry.first == _valueId; }) != liveCounts.end();
}

SSACFGLiveness::LivenessData::Count SSACFGLiveness::LivenessData::count(SSACFG::ValueId const& _valueId) const
{
	auto it = ranges::find_if(liveCounts, [&](auto const& entry) { return entry.first == _valueId; });
	if (it != liveCounts.end())
		return it->second;
	return 0;
}

SSACFGLiveness::LivenessData::LiveCounts::const_iterator SSACFGLiveness::LivenessData::begin() const
{
	return liveCounts.begin();
}

SSACFGLiveness::LivenessData::LiveCounts::const_iterator SSACFGLiveness::LivenessData::end() const
{
	return liveCounts.end();
}

SSACFGLiveness::LivenessData::LiveCounts::size_type SSACFGLiveness::LivenessData::size() const
{
	return liveCounts.size();
}

bool SSACFGLiveness::LivenessData::empty() const { return liveCounts.empty(); }
void SSACFGLiveness::LivenessData::insert(Value const& _value, Count _count)
{
	if (_count == 0)
		return;

	auto it = findEntry(_value);
	if (it != liveCounts.end())
		it->second += _count;
	else
		liveCounts.emplace_back(_value, _count);
}
SSACFGLiveness::LivenessData& SSACFGLiveness::LivenessData::maxUnion(LivenessData const& _other)
{
	for (auto const& [value, count]: _other.liveCounts)
	{
		auto it = findEntry(value);
		if (it != liveCounts.end())
			it->second = std::max(it->second, count);
		else
			liveCounts.emplace_back(value, count);
	}
	return *this;
}
SSACFGLiveness::LivenessData& SSACFGLiveness::LivenessData::operator+=(LivenessData const& _other)
{
	for (auto const& entry : _other.liveCounts)
		insert(entry.first, entry.second);
	return *this;
}

SSACFGLiveness::LivenessData& SSACFGLiveness::LivenessData::operator-=(LivenessData const& _other)
{
	std::erase_if(liveCounts, [&](auto const& entry) { return _other.contains(entry.first); });
	return *this;
}
void SSACFGLiveness::LivenessData::erase(Value const& _value)
{
	auto it = findEntry(_value);
	if (it != liveCounts.end())
		liveCounts.erase(it);
}
void SSACFGLiveness::LivenessData::remove(Value const& _value, Count _count)
{
	if (_count == 0)
		return;

	auto it = findEntry(_value);
	if (it != liveCounts.end())
	{
		if (it->second <= _count)
			liveCounts.erase(it);
		else
			it->second -= _count;
	}
}

SSACFGLiveness::LivenessData SSACFGLiveness::blockExitValues(SSACFG::BlockId const& _blockId) const
{
	LivenessData result;
	util::GenericVisitor exitVisitor{
		[](SSACFG::BasicBlock::MainExit const&) {},
		[&](SSACFG::BasicBlock::FunctionReturn const& _functionReturn)
		{
			for (auto const& valueId: _functionReturn.returnValues | ranges::views::filter(literalsFilter(m_cfg)))
				result.insert(valueId);
		},
		[&](SSACFG::BasicBlock::JumpTable const& _jt)
		{
			if (literalsFilter(m_cfg)(_jt.value))
				result.insert(_jt.value);
		},
		[](SSACFG::BasicBlock::Jump const&) {},
		[&](SSACFG::BasicBlock::ConditionalJump const& _conditionalJump)
		{
			if (literalsFilter(m_cfg)(_conditionalJump.condition))
				result.insert(_conditionalJump.condition);
		},
		[](SSACFG::BasicBlock::Terminated const&) {}};
	std::visit(exitVisitor, m_cfg.block(_blockId).exit);
	return result;
}



SSACFGLiveness::SSACFGLiveness(SSACFG const& _cfg):
	m_cfg(_cfg),
	m_topologicalSort(_cfg),
	m_loopNestingForest(m_topologicalSort),
	m_liveIns(_cfg.numBlocks()),
	m_liveOuts(_cfg.numBlocks()),
	m_operationLiveOuts(_cfg.numBlocks())
{
	runDagDfs();
	for (auto const loopRootNode: m_loopNestingForest.loopRootNodes())
		runLoopTreeDfs(loopRootNode);

	fillOperationsLiveOut();
}

SSACFGLiveness::LivenessData SSACFGLiveness::used(SSACFG::BlockId const _blockId) const
{
	auto used = liveIn(_blockId);
	for (auto const& [valueId, count] : liveOut(_blockId))
		used.remove(valueId, count);
	return used;
}

void SSACFGLiveness::runDagDfs()
{
	// SSA Book, Algorithm 9.2
	for (auto const blockIdValue: m_topologicalSort.postOrder())
	{
		// post-order traversal
		SSACFG::BlockId blockId{blockIdValue};
		auto const& block = m_cfg.block(blockId);

		// live <- PhiUses(B)
		LivenessData live{};
		block.forEachExit(
			[&](SSACFG::BlockId const& _successor)
			{
				for (auto const& phi: m_cfg.block(_successor).phis)
				{
					auto const& info = m_cfg.valueInfo(phi);
					yulAssert(std::holds_alternative<SSACFG::PhiValue>(info), "value info of phi wasn't PhiValue");
					auto const argIndex = m_cfg.phiArgumentIndex(blockId, _successor);
					yulAssert(argIndex < std::get<SSACFG::PhiValue>(info).arguments.size());
					auto const arg = std::get<SSACFG::PhiValue>(info).arguments.at(argIndex);
					if (!std::holds_alternative<SSACFG::LiteralValue>(m_cfg.valueInfo(arg)))
						live.insert(arg);
				}
			});

		// for each S \in succs(B) s.t. (B, S) not a back edge: live <- live \cup (LiveIn(S) - PhiDefs(S))
		block.forEachExit(
			[&](SSACFG::BlockId const& _successor) {
				if (!m_topologicalSort.backEdge(blockId, _successor))
				{
					// LiveIn(S) - PhiDefs(S)
					auto liveInWithoutPhiDefs = m_liveIns[_successor.value];
					for (auto const& phiId: m_cfg.block(_successor).phis)
						liveInWithoutPhiDefs.erase(phiId);
					live += liveInWithoutPhiDefs;
				}
			});

		if (std::holds_alternative<SSACFG::BasicBlock::FunctionReturn>(block.exit))
			for (auto const& returnValue: std::get<SSACFG::BasicBlock::FunctionReturn>(block.exit).returnValues | ranges::views::filter(literalsFilter(m_cfg)))
				live.insert(returnValue);

		// clean out unreachables
		live.eraseIf([&](auto const& _entry) { return !unreachableFilter(m_cfg)(_entry.first); });

		// LiveOut(B) <- live
		m_liveOuts[blockId.value] = live;

		// for each program point p in B, backwards, do:
		{
			// add value ids to the live set that are used in exit blocks
			live += blockExitValues(blockId);

			for (auto const& op: block.operations | ranges::views::reverse)
			{
				// remove variables defined at p from live
				live.eraseAll(op.outputs | ranges::views::filter(literalsFilter(m_cfg)) | ranges::to<std::vector>);
				// add uses at p to live
				live.insertAll(op.inputs | ranges::views::filter(literalsFilter(m_cfg)) | ranges::to<std::vector>);
			}
		}

		// livein(b) <- live \cup PhiDefs(B)
		for (auto const& phi: block.phis)
			live.insert(phi);
		m_liveIns[blockId.value] = live;
	}
}

void SSACFGLiveness::runLoopTreeDfs(size_t const _loopHeader)
{
	// SSA Book, Algorithm 9.3
	if (m_loopNestingForest.loopNodes().contains(_loopHeader))
	{
		// the loop header block id
		auto const& block = m_cfg.block(SSACFG::BlockId{_loopHeader});
		// LiveLoop <- LiveIn(B_N) - PhiDefs(B_N)
		auto liveLoop = m_liveIns[_loopHeader];
		for (auto const& phi: block.phis)
			liveLoop.erase(phi);
		// must be live out of header if live in of children
		m_liveOuts[_loopHeader].maxUnion(liveLoop);
		// for each blockId \in children(loopHeader)
		for (size_t blockIdValue = 0; blockIdValue < m_cfg.numBlocks(); ++blockIdValue)
			if (m_loopNestingForest.loopParents()[blockIdValue] == _loopHeader)
			{
				// propagate loop liveness information down to the loop header's children
				m_liveIns[blockIdValue].maxUnion(liveLoop);
				m_liveOuts[blockIdValue].maxUnion(liveLoop);

				runLoopTreeDfs(blockIdValue);
			}
	}
}

void SSACFGLiveness::fillOperationsLiveOut()
{
	for (SSACFG::BlockId blockId{0}; blockId.value < m_cfg.numBlocks(); ++blockId.value)
	{
		auto const& operations = m_cfg.block(blockId).operations;
		auto& liveOuts = m_operationLiveOuts[blockId.value];
		liveOuts.resize(operations.size());
		if (!operations.empty())
		{
			auto live = m_liveOuts[blockId.value];
			live += blockExitValues(blockId);
			auto rit = liveOuts.rbegin();
			for (auto const& op: operations | ranges::views::reverse)
			{
				*rit = live;
				auto const operationInputs = op.inputs | ranges::views::filter(literalsFilter(m_cfg)) | ranges::to<std::vector>;
				for (auto const& output: op.outputs | ranges::views::filter(literalsFilter(m_cfg)))
					live.erase(output);
				for (auto const input: operationInputs)
					live.insert(input);
				++rit;
			}
		}
	}
}
