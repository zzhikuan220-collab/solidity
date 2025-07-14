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

#include <test/TestCase.h>

#include <libyul/backends/evm/ControlFlowGraph.h>
#include <libyul/backends/evm/SSACFGStack.h>

#include <map>

using namespace solidity::frontend::test;

namespace solidity::yul::test
{
using TestSlot = std::variant<SSACFG::ValueId, ssa::JunkSlot>;
struct PrintCallback
{
	using Slot = TestSlot;
	void swap(size_t)
	{
		++numOps;
	}
	void dup(size_t)
	{
		++numOps;
	}
	void push(Slot const&)
	{
		++numOps;
	}
	void pop()
	{
		++numOps;
	}

	size_t numOps{};
	//todo ssa::Stack<PrintCallback>* self;
};
struct SlotCanBeFreelyGenerated
{
	using Slot = TestSlot;
	bool operator()(Slot const& _slot) const
	{
		if (std::holds_alternative<SSACFG::ValueId>(_slot))
			return m_cfg->isLiteralValue(std::get<SSACFG::ValueId>(_slot));
		return std::holds_alternative<ssa::JunkSlot>(_slot);
	}

	SSACFG const* m_cfg;
};
class SSAStackShufflingTest final: public TestCase
{
	using Stack = ssa::Stack<TestSlot, PrintCallback, SlotCanBeFreelyGenerated>;
public:
	static std::unique_ptr<TestCase> create(Config const& _config)
	{
		return std::make_unique<SSAStackShufflingTest>(_config.filename);
	}
	explicit SSAStackShufflingTest(std::string const& _filename);
	~SSAStackShufflingTest() override;
	TestResult run(std::ostream& _stream, std::string const& _linePrefix = "", bool _formatted = false) override;
private:
	void processSettings();
	Stack::Data parse(std::string const& _source);

	size_t m_maximumStackDepth{};
	std::unique_ptr<SSACFG> m_cfg;
	Stack::Data m_sourceData;
	Stack m_sourceStack;
	Stack::Data m_targetData;
	Stack m_targetStack;
	std::map<std::string, FunctionCall> m_functions;
	std::map<std::string, Scope::Variable> m_variables;
};
}
