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

#include <map>

using namespace solidity::frontend::test;

namespace solidity::yul::test
{

class SSAStackShufflingTest final: public TestCase
{
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
	bool parse(std::string const& _source);

	size_t m_maximumStackDepth{};
	Stack m_sourceStack;
	Stack m_targetStack;
	std::map<YulName, FunctionCall> m_functions;
	std::map<YulName, Scope::Variable> m_variables;
};
}
