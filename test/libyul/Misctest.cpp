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

using TestStack = solidity::yul::ssa::Stack<SourceSlot, PrintCallback, SlotCanBeFreelyGenerated>;



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

	// stack->push(cfg->newLiteral(langutil::DebugData::create(), 42));
	auto const v0 = cfg->newVariable({0});
	auto const v1 = cfg->newVariable({0});
	auto const v2 = cfg->newVariable({0});
	auto const v3 = cfg->newVariable({0});
	auto const v4 = cfg->newVariable({0});
	auto const v5 = cfg->newVariable({0});
	auto const v6 = cfg->newVariable({0});
	auto const v98 = cfg->newVariable({0});
	auto const v99 = cfg->newVariable({0});
	auto const v187 = cfg->newVariable({0});
	auto const v188 = cfg->newVariable({0});

	// calldatacopy([v0, v1, v2, v3, v4, v5, v6, v98, v99, v187, v188] -> { [v1, v2, v3, v4, v5, v6, v98, v99, v187, v188] } + [v1, v0, v188])

	stack->push(v0);
	stack->push(v1);
	stack->push(v2);
	stack->push(v3);
	stack->push(v4);
	stack->push(v5);
	stack->push(v6);
	stack->push(v98);
	stack->push(v99);
	stack->push(v187);
	stack->push(v188);

	std::cout << "--- start shuffle ---" << std::endl;
	// *stack = DanielShuffler<TestStack>::shuffle(*stack, {v1, v2, v3, v4, v5, v6, v98, v99, v187, v188}, {v1, v0, v188});
	static auto constexpr slotCompatible = [](SourceSlot const& _s1, SourceSlot const& _s2) { return _s1 == _s2; };
	BlockForwardShuffler<TestStack, slotCompatible>::shuffle(*stack, {v1, v2, v3, v4, v5, v6, v98, v99, v187, v188}, {v1, v0, v188});
	std::cout << "--- fin ---" << std::endl;
	std::cout << ssa::stackToString(stack->data(), *cfg) << std::endl;
}

BOOST_AUTO_TEST_SUITE_END()
}
