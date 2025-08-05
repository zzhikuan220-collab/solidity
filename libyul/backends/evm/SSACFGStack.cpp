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

#include <libyul/backends/evm/SSACFGStack.h>

#include <libsolutil/Visitor.h>

#include <range/v3/view/drop.hpp>

using namespace solidity;
using namespace solidity::yul;
using namespace solidity::yul::ssa;

std::string ssa::slotToString(StackSlot const& _slot, SSACFG const& _cfg)
{
	return std::visit(util::GenericVisitor{
		[&](SSACFG::ValueId const _value) {
			return _cfg.valueDescription(_value);
		},
		[](AbstractAssembly::LabelID const _label) {
			return "LABEL[" + std::to_string(_label) + "]";
		},
		[](FunctionReturnLabel const& _functionReturnLabel)
		{
			yulAssert(_functionReturnLabel.functionCall, "Function return label was null.");
			yulAssert(std::holds_alternative<Identifier>(_functionReturnLabel.functionCall->functionName));
			return fmt::format("ReturnLabel[{}]", std::get<Identifier>(_functionReturnLabel.functionCall->functionName).name.str());
		},
		[](JunkSlot const&) -> std::string
		{
			return "JUNK";
		}
	}, _slot);
}

std::string ssa::stackToString(StackData const& _stackData, SSACFG const& _cfg)
{
	auto const numJunk = junkTailSize(_stackData);
	if (numJunk > 0)
		return format(
			"[JUNK x {}, {}]",
			numJunk,
			fmt::join(_stackData | ranges::views::drop(numJunk) | ranges::views::transform([&](auto const& _slot) { return slotToString(_slot, _cfg); }), ", ")
		);
	else
		return format(
			"[{}]",
			fmt::join(_stackData | ranges::views::transform([&](auto const& _slot) { return slotToString(_slot, _cfg); }), ", ")
		);
}
