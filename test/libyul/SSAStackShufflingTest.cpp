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

#if defined(__GNUC__) && !defined(__clang__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
#include <memory>
#pragma GCC diagnostic pop
#endif

#include <test/libyul/SSAStackShufflingTest.h>

#include <test/Common.h>

#include <libyul/backends/evm/SSACFGStack.h>
#include <libyul/backends/evm/SSACFGStackLayout.h>

#include <liblangutil/Scanner.h>
#include <libsolutil/AnsiColorized.h>
#include <libsolutil/StringUtils.h>

using namespace solidity::test;
using namespace solidity::util;
using namespace solidity::langutil;
using namespace solidity::yul;
using namespace solidity::yul::test;

SSAStackShufflingTest::Stack::Data SSAStackShufflingTest::parse(std::string const& _source)
{
	CharStream stream(_source, "");
	Scanner scanner(stream);

	Stack::Data stackData;

	if (scanner.currentToken() != Token::LBrack)
		throw std::runtime_error("Invalid token.");
	scanner.next();
	while (scanner.currentToken() != Token::RBrack &&
		   scanner.currentToken() != Token::EOS)
	{
		std::string literal = scanner.currentLiteral();
		if (literal.find("0x") != std::string::npos || scanner.currentToken() == Token::Number)
			stackData.emplace_back(m_cfg->newLiteral(DebugData::create(), u256(literal)));
		else if (literal == "JUNK")
			stackData.emplace_back(ssa::JunkSlot{});
		else
			stackData.emplace_back(m_cfg->newVariable({0}));
		scanner.next();
	}
	if (scanner.currentToken() != Token::RBrack)
		throw std::runtime_error("Invalid token.");

	scanner.next();

	return stackData;
}

SSAStackShufflingTest::SSAStackShufflingTest(std::string const& _filename):
	TestCase(_filename),
	m_cfg([]
	{
		auto cfg = std::make_unique<SSACFG>();
		cfg->debugData = DebugData::create();
		cfg->entry = cfg->makeBlock(DebugData::create());
		cfg->block(cfg->entry).exit = SSACFG::BasicBlock::MainExit{};
		return cfg;
	}()),
	m_sourceStack(parse(m_reader.source()), {}, {&*m_cfg}),
	m_targetStack(parse(m_reader.source()), {}, {&*m_cfg})
{
	processSettings();
	m_source = m_reader.source();
	m_expectation = m_reader.simpleExpectations();
}

SSAStackShufflingTest::~SSAStackShufflingTest() = default;

void SSAStackShufflingTest::processSettings()
{
	std::string depthString = m_reader.stringSetting("maximumStackDepth", "16");
	std::optional<unsigned> depth = toUnsignedInt(depthString);
	if (!depth.has_value())
		BOOST_THROW_EXCEPTION(std::runtime_error{"Invalid maximum stack depth: \"" + depthString + "\""});
	m_maximumStackDepth = *depth;
}

TestCase::TestResult SSAStackShufflingTest::run(std::ostream& _stream, std::string const& _linePrefix, bool _formatted)
{
	_stream << _linePrefix << _formatted;
	/*auto const& dialect = CommonOptions::get().evmDialect();
	if (!parse(m_source))
	{
		AnsiColorized(_stream, _formatted, {formatting::BOLD, formatting::RED}) << _linePrefix << "Error parsing source." << std::endl;
		return TestResult::FatalError;
	}

	std::ostringstream output;
	size_t operations = 0;
	// todo insert daniel shuffler here
	createStackLayout(
		m_sourceStack,
		m_targetStack,
		[&](unsigned _swapDepth) // swap
		{
			++operations;
			output << stackToString(m_sourceStack, dialect) << std::endl;
			output << "SWAP" << _swapDepth << std::endl;
		},
		[&](StackSlot const& _slot) // dupOrPush
		{
			++operations;
			output << stackToString(m_sourceStack, dialect) << std::endl;
			if (canBeFreelyGenerated(_slot))
				output << "PUSH " << stackSlotToString(_slot, dialect) << std::endl;
			else
			{
				if (auto depth = util::findOffset(m_sourceStack | ranges::views::reverse, _slot))
					output << "DUP" << *depth + 1 << std::endl;
				else
					BOOST_THROW_EXCEPTION(std::runtime_error("Invalid DUP operation."));
			}
		},
		[&](){ // pop
			++operations;
			output << stackToString(m_sourceStack, dialect) << std::endl;
			output << "POP" << std::endl;
		},
		m_maximumStackDepth
    );

	output << stackToString(m_sourceStack, dialect) << std::endl;
	output << operations << " operations" << std::endl;
	m_obtainedResult = output.str();

	return checkResult(_stream, _linePrefix, _formatted);*/
	return {};
}
