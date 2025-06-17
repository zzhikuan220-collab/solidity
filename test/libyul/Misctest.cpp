#include <boost/test/unit_test.hpp>

#include <libyul/backends/evm/SSACFGLiveness.h>
#include <libyul/backends/evm/SSACFGStack.h>
#include <libyul/backends/evm/SSACFGStackShuffler.h>

#include <range/v3/view/concat.hpp>

namespace
{

using SourceSlot = solidity::yul::ssa::StackSlot;
using TargetSlot = SourceSlot;
struct PrintCallback
{
	PrintCallback(std::function<void()> _callback): callback(_callback) {}

	using Slot = SourceSlot;
	void swap(size_t _depth)
	{
		++numOps;
		fmt::print("swap {}: ", _depth);
		callback();
	}
	void dup(size_t _depth)
	{
		++numOps;
		fmt::print("dup {}: ", _depth);
		callback();
	}
	void push(Slot const&)
	{
		++numOps;
		fmt::print("push: ");
		callback();
	}
	void pop()
	{
		++numOps;
		fmt::print("pop: ");
		callback();
	}

	size_t numOps{};
	std::function<void()> callback;
};

struct SlotCanBeFreelyGenerated
{
	using Slot = SourceSlot;
	bool operator()(Slot const& _slot) const
	{
		return canBeFreelyGenerated(_slot);
	}

	solidity::yul::ssa::SlotCanBeFreelyGenerated<solidity::yul::ssa::StackSlot> canBeFreelyGenerated;
};

using TestStack = solidity::yul::ssa::Stack<PrintCallback, SlotCanBeFreelyGenerated>;



}

namespace solidity::yul::test
{
BOOST_AUTO_TEST_SUITE(MiscTest)

BOOST_AUTO_TEST_CASE(yo)
{
	auto cfg = std::make_unique<SSACFG>();
	cfg->debugData = langutil::DebugData::create();
	cfg->entry = cfg->makeBlock(langutil::DebugData::create());
	cfg->block(cfg->entry).exit = SSACFG::BasicBlock::MainExit{};

	std::shared_ptr<TestStack> stack;
	std::vector<SourceSlot> slots;
	PrintCallback callback([&stack, &cfg]
	{
		if (stack)
			std::cout << ssa::stackToString(stack->data(), *cfg) << std::endl;
	});
	SlotCanBeFreelyGenerated canBeFreelyGenerated{.canBeFreelyGenerated = {cfg.get()}};
	stack = std::make_shared<TestStack>(slots, callback, canBeFreelyGenerated);

	stack->push(cfg->newLiteral(langutil::DebugData::create(), 42));
	auto const v1 = cfg->newVariable({0});
	auto const v2 = cfg->newVariable({0});
	auto const v3 = cfg->newVariable({0});

	stack->push(v1);
	stack->push(v3);
	stack->push(v2);

	std::cout << "--- start shuffle ---" << std::endl;
	BlockForwardShuffler<TestStack>::shuffle(*stack, {v2, v1}, {v3});
	std::cout << "--- fin ---" << std::endl;
	std::cout << ssa::stackToString(stack->data(), *cfg) << std::endl;
}

BOOST_AUTO_TEST_SUITE_END()
}
