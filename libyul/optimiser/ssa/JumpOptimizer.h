#pragma once

#include <libyul/backends/evm/SSAControlFlowGraph.h>

namespace solidity::yul::ssa
{

inline SSACFG optimizeJumps(SSACFG const& _cfg)
{
	for (SSACFG::BlockId blockId{0}; blockId.value < _cfg.numBlocks(); ++blockId.value)
	{
		auto const& block = _cfg.block(blockId);
		if (block.phis.empty() && std::holds_alternative<SSACFG::BasicBlock::Jump>(block.exit))
		{
			// todo
		}
	}
}

}
