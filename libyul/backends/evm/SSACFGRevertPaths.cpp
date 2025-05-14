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

#include <libyul/backends/evm/SSACFGRevertPaths.h>

#include <libyul/backends/evm/SSACFGBridgeFinder.h>

namespace solidity::yul
{

SSACFGRevertPaths::SSACFGRevertPaths(SSACFG const& _cfg, ForwardSSACFGTopologicalSort const& _topologicalSort):
	m_blockIsOnRevertPath(_cfg.numBlocks(), false)
{
	SSACFGBridgeFinder const bridgeFinder(_cfg);

	std::vector<SSACFG::BlockId> terminateBlocks;
	std::vector<SSACFG::BlockId> functionReturns;
	for (auto const blockIndex: _topologicalSort.preOrder())
	{
		auto const& block = _cfg.block(SSACFG::BlockId{blockIndex});
		if (block.isTerminationBlock() || block.isMainExitBlock())
			terminateBlocks.emplace_back(SSACFG::BlockId{blockIndex});
		if (block.isFunctionReturnBlock())
			functionReturns.emplace_back(SSACFG::BlockId{blockIndex});
	}

	for (auto const& terminateBlock: terminateBlocks)
	{
		std::vector<uint8_t> visited(_cfg.numBlocks(), false);
		std::vector toVisit{terminateBlock};
		while (!toVisit.empty())
		{
			auto const blockId = toVisit.back();
			auto const& block = _cfg.block(blockId);
			toVisit.pop_back();

			bool const containedInRevertPath = bridgeFinder.bridgeVertex(blockId); // ranges::all_of(block.entries, [&](SSACFG::BlockId const& _entry) { return bridgeFinder.bridgeVertex(_entry); });
			m_blockIsOnRevertPath[blockId.value] = containedInRevertPath;
			visited[blockId.value] = true;
			if (!containedInRevertPath)
				continue;

			for (auto const& entry: block.entries)
				if (!visited[entry.value] && bridgeFinder.bridgeVertex(entry))
					toVisit.emplace_back(entry);
		}
	}

	for (auto const& returnBlock: functionReturns)
	{
		std::vector<uint8_t> visited(_cfg.numBlocks(), false);
		std::vector toVisit{returnBlock};

		while (!toVisit.empty())
		{
			auto const blockId = toVisit.back();
			auto const& block = _cfg.block(blockId);
			toVisit.pop_back();

			m_blockIsOnRevertPath[blockId.value] = false;
			visited[blockId.value] = true;
			for (auto const& entry: block.entries)
				if (!visited[entry.value])
					toVisit.emplace_back(entry);
		}
	}
}

bool SSACFGRevertPaths::blockIsOnRevertPath(SSACFG::BlockId const& _blockId) const
{
	return m_blockIsOnRevertPath[_blockId.value];
}

}
