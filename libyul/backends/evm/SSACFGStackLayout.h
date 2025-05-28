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

#include <libyul/backends/evm/AbstractAssembly.h>
#include <libyul/backends/evm/SSACFGStack.h>
#include <libyul/backends/evm/SSAControlFlowGraph.h>

#include <libyul/Exceptions.h>

#include <range/v3/view/reverse.hpp>

#include <map>
#include <range/v3/algorithm/count_if.hpp>
#include <variant>
#include <vector>

namespace solidity::yul::ssa
{
/// If Block `_from` -> Block `_to` and `_to` has phi functions `v_k := phi(..., _from => v_i, ...)`, this transform
/// pulls values `v_k` back to `v_i`.
class ReversePhiFunctionTransform
{
public:
	ReversePhiFunctionTransform() = default;
	ReversePhiFunctionTransform(SSACFG const& _cfg, SSACFG::BlockId _from, SSACFG::BlockId _to);

	/// whether the transform is guaranteed to be a no-op, ie, there is no phi function in `_to`
	bool noOp() const;
	SSACFG::ValueId operator()(SSACFG::ValueId _valueId) const;

	// if we have a variant with value id contained in the type union
	template<typename... T>
	std::variant<T...> operator()(std::variant<T...> const& _someSlot) const
	{
		static bool constexpr variantContainsValueId = std::disjunction_v<std::is_same<SSACFG::ValueId, T>...>;
		static_assert(variantContainsValueId);
		if (auto valueId = std::get_if<SSACFG::ValueId>(&_someSlot))
			return (*this)(*valueId);
		return _someSlot;
	}

private:
	std::map<SSACFG::ValueId, SSACFG::ValueId> m_reversePhiMap = {};
};



struct SSACFGStackLayout
{
	// each operation has a current stack
	using Stack = StackData;
	// a slot can be some valueId or a labelId
	using Slot = Stack::value_type;

	// Each block has its own layout
	struct BlockLayout
	{
		// stack layout required to enter the block
		Stack stackIn;
		// stack layout required to execute the i-th operation in the block
		std::vector<Stack> operationIn;
		// stack after the block was executed
		Stack stackOut;
	};

	// each block has a fixed list of operations
	using BlockLayouts = std::vector<BlockLayout>;

	BlockLayout& operator[](SSACFG::BlockId const _blockId)
	{
		yulAssert(_blockId.value < blockLayouts.size());
		return blockLayouts[_blockId.value];
	}

	BlockLayout const& operator[](SSACFG::BlockId const _blockId) const
	{
		yulAssert(_blockId.value < blockLayouts.size());
		return blockLayouts[_blockId.value];
	}

	BlockLayouts blockLayouts;
};

struct ControlFlowLayout
{
	SSACFGStackLayout mainLayout;
	std::vector<SSACFGStackLayout> functionLayouts;
};
}
