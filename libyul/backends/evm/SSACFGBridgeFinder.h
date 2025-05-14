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

#include <libyul/backends/evm/SSAControlFlowGraph.h>

#include <range/v3/view/concat.hpp>

#include <cstdint>
#include <optional>
#include <vector>

namespace solidity::yul
{
/// Detect bridges according to Algorithm 1 of https://arxiv.org/pdf/2108.07346.pdf
class SSACFGBridgeFinder
{
public:
	explicit SSACFGBridgeFinder(SSACFG const& _cfg):
		m_cfg(_cfg),
		m_bridgeVertex(_cfg.numBlocks()),
		m_visited(_cfg.numBlocks()),
		m_disc(_cfg.numBlocks()),
		m_low(_cfg.numBlocks())
	{
		size_t time = 0;
		dfs(time, _cfg.entry, std::nullopt);
	}

	bool bridgeVertex(SSACFG::BlockId const& _blockId) const
	{
		return m_bridgeVertex[_blockId.value];
	}

private:
	void dfs(size_t& _time, SSACFG::BlockId const& _vertex, std::optional<SSACFG::BlockId> const& _parent)
	{
		m_visited[_vertex.value] = true;
		m_disc[_vertex.value] = _time;
		m_low[_vertex.value] = _time;
		++_time;

		auto const& currentBlock = m_cfg.block(_vertex);
		std::vector<SSACFG::BlockId> adjacentExitVertices;
		currentBlock.forEachExit([&](SSACFG::BlockId const& _exit)
		{
			adjacentExitVertices.emplace_back(_exit);
		});

		for (SSACFG::BlockId const neighbor: ranges::views::concat(adjacentExitVertices, currentBlock.entries))
		{
			if (neighbor == _parent)
				continue;

			if (!m_visited[neighbor.value])
			{
				dfs(_time, neighbor, _vertex);
				m_low[_vertex.value] = std::min(m_low[_vertex.value], m_low[neighbor.value]);
				if (m_low[neighbor.value] > m_disc[_vertex.value])
				{
					// vertex <-> neighbor is a bridge in the undirected graph
					bool const edgeNeighborToVertex = currentBlock.entries.contains(neighbor);
					bool const edgeVertexToNeighbor = m_cfg.block(neighbor).entries.contains(_vertex);

					// special case: if it's the entry itself, we mark it as bridge vertex (provided correct orientation),
					// so that functions which do nothing but revert have their whole tree marked as such (sans loops)
					// todo correct?
					if (!_parent)
						m_bridgeVertex[_vertex.value] = edgeVertexToNeighbor;
					// Since we are not really undirected, check if we don't have a cycle (u -> v and v -> u) and see,
					// which edge really exists here.
					// Then record the targeted vertex as bridge vertex.
					if (edgeVertexToNeighbor && !edgeNeighborToVertex)
						// bridge vertex -> neighbor
						m_bridgeVertex[neighbor.value] = true;
					else if (edgeNeighborToVertex && !edgeVertexToNeighbor)
						// bridge neighbor -> vertex
						m_bridgeVertex[_vertex.value] = true;
				}
			}
			else
				m_low[_vertex.value] = std::min(m_low[_vertex.value], m_disc[neighbor.value]);
		}
	}

	SSACFG const& m_cfg;
	std::vector<std::uint8_t> m_bridgeVertex;
	std::vector<std::uint8_t> m_visited;
	std::vector<std::size_t> m_disc;
	std::vector<std::size_t> m_low;
};

}
