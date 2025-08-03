#include "libyul/backends/evm/SSACFGStackShuffler.h"
#include "range/v3/algorithm/none_of.hpp"


#include <libyul/backends/evm/ssa/StackLayoutGenerator.h>
#include <queue>
#include <ranges>

using namespace solidity::yul;
using namespace solidity::yul::ssa;

namespace
{
#if !defined(NDEBUG)
bool constexpr debugOutput = true;
#else
bool constexpr debugOutput = true;
#endif
template<typename Slot>
[[maybe_unused]] std::vector<Slot> pileOfJunk(size_t const _size)
{
	return std::vector<Slot>(_size, ssa::JunkSlot{});
}

template<typename StackData>
size_t junkTailSize(StackData const& _stackData)
{
	std::size_t numJunk = 0;
	auto it = _stackData.begin();
	while (it != _stackData.end() && std::holds_alternative<ssa::JunkSlot>(*it))
	{
		++numJunk;
		++it;
	}
	return numJunk;
}

/*class IsSSACFGLiteral
{
public:
	explicit IsSSACFGLiteral(SSACFG const& _cfg): m_cfg(_cfg) {}

	bool operator()(SSACFG::ValueId const _valueId) const { return m_cfg.isLiteralValue(_valueId); }
	bool operator()(SSACFGStackLayout::Slot const& _slot) const
	{
		return std::holds_alternative<SSACFG::ValueId>(_slot) && (*this)(std::get<SSACFG::ValueId>(_slot));
	}

private:
	SSACFG const& m_cfg;
};*/
}

StackLayoutGenerator::StackLayoutGenerator(SSACFGLiveness const& _liveness):
	m_liveness(_liveness),
	m_cfg(_liveness.cfg()),
	m_blockIsGenerated(m_cfg.numBlocks(), false),
	m_blockHasStackInDefined(m_cfg.numBlocks(), false),
	m_junkBlockFinder(_liveness.cfg(), _liveness.topologicalSort())
{
	m_stackLayout.blockLayouts.resize(m_cfg.numBlocks());
}

ControlFlowLayout StackLayoutGenerator::generate(ControlFlowLiveness const& _controlFlowLiveness)
{
	ControlFlowLayout layout;
	layout.mainLayout = generate(*_controlFlowLiveness.mainLiveness);

	layout.functionLayouts.reserve(_controlFlowLiveness.functionLiveness.size());
	for (auto const& functionLiveness: _controlFlowLiveness.functionLiveness)
		layout.functionLayouts.push_back(generate(*functionLiveness));

	return layout;
}

SSACFGStackLayout StackLayoutGenerator::generate(SSACFGLiveness const& _cfgLiveness)
{
	if constexpr (debugOutput)
		std::cout << "stack layout for " << (_cfgLiveness.cfg().function ? _cfgLiveness.cfg().function->name.str() : "main graph") << '\n';
	return StackLayoutGenerator{_cfgLiveness}.computeStackLayout();
}

SSACFGStackLayout const& StackLayoutGenerator::computeStackLayout()
{
	// traverse the cfg layer-wise using Kahn's algorithm
	// like this, (most of) the entry exit layouts are known when a block is processed

	std::vector<std::size_t> inDegreesIgnoringBackedges(m_cfg.numBlocks(), 0);

	for (SSACFG::BlockId id{0}; id.value < m_cfg.numBlocks(); ++id.value)
		for (auto const& entry: m_cfg.block(id).entries)
			if (!m_liveness.topologicalSort().backEdge(entry, id))
				inDegreesIgnoringBackedges[id.value] += 1;

	std::queue<SSACFG::BlockId> traversalQueue;
	traversalQueue.push(m_cfg.entry);

	size_t numVisited = 0;
	while (!traversalQueue.empty())
	{
		auto currentBlockId = traversalQueue.front();
		traversalQueue.pop();

		visitBlock(currentBlockId);

		m_cfg.block(currentBlockId).forEachExit([&](SSACFG::BlockId const& _exit){
			if (--inDegreesIgnoringBackedges[_exit.value] == 0)
				traversalQueue.push(_exit);
		});
		++numVisited;
	}
	yulAssert(numVisited == m_liveness.topologicalSort().preOrder().size());

	// todo unnecessary copy here
	return m_stackLayout;
}

void StackLayoutGenerator::defineStackIn(SSACFG::BlockId const& _blockId)
{
	if (_blockId == m_cfg.entry)
	{
		if (!m_cfg.function)
			m_stackLayout[m_cfg.entry].stackIn = {};
		else
			m_stackLayout[m_cfg.entry].stackIn =
				m_cfg.arguments |
				ranges::views::reverse |
				ranges::views::transform([](auto&& _variableAndValueId) -> Slot { return std::get<1>(_variableAndValueId); }) |
				ranges::to<std::vector>;
		m_blockHasStackInDefined[_blockId.value] = true;
		return;
	}

	auto const& block = m_cfg.block(_blockId);

	std::vector<StackData const*> parentExits;
	for (auto const& entry: block.entries)
		if (m_blockIsGenerated[entry.value])
			parentExits.push_back(&m_stackLayout[entry].stackOut);

	yulAssert(!parentExits.empty(), fmt::format("None of the parents of block {} were generated", _blockId));

	if (block.entries.size() == 1)
	{
		// pass through
		yulAssert(block.phis.empty());
		yulAssert(parentExits.size() == 1);
		m_stackLayout[_blockId].stackIn = *parentExits[0];
	}
	else
	{
		// we have more than one entry and need to unify or at the very least apply phi fct.
		auto const& liveIn = m_liveness.liveIn(_blockId);
		auto usedVariables = m_liveness.used(_blockId);

		// todo use the most fitting one
		//		from grey approach and each of the predecessor stacks
		// phis at the top
		std::vector<Slot> unifiedStack(block.phis.begin(), block.phis.end());
		// then all variables that are used
		// todo could be sorted by usage frequency
		for (auto const& [var, numUsed]: usedVariables)
			if (!block.phis.contains(var))
				unifiedStack.emplace_back(var);
		// then all variables that are live in but not used
		// todo could be sorted by usage frequency
		for (auto const& [var, numUsed]: liveIn)
			if (!block.phis.contains(var) && !usedVariables.contains(var))
				unifiedStack.emplace_back(var);

		// todo junk

		/*StackData unifiedStack;
		for (auto targetVar : targetStackLayout) {
			// Case 1: Phi function mapping
			if (auto phiInput = getPhiMapping(targetVar, predecessorId)) {
				unifiedStack.push_back(*phiInput);
			}
			// Case 2: Direct variable (if live in this predecessor)
			else if (isLiveInPredecessor(targetVar, predecessorId)) {
				unifiedStack.push_back(targetVar);
			}
			// Case 3: Skip! (no "bottom" needed)
		}*/
		m_stackLayout[_blockId].stackIn = unifiedStack | ranges::views::reverse | ranges::to<std::vector>;
	}

	m_blockHasStackInDefined[_blockId.value] = true;
}

void StackLayoutGenerator::visitBlock(SSACFG::BlockId const& _blockId)
{
	yulAssert(!m_blockIsGenerated[_blockId.value]);
	defineStackIn(_blockId);
	yulAssert(m_blockHasStackInDefined[_blockId.value]);

	StackData currentStackData = m_stackLayout[_blockId].stackIn;
	StackType stack(currentStackData, {}, {&m_cfg});
	bool const junkCanBeAdded = m_junkBlockFinder.blockAllowsAdditionOfJunk(_blockId);
	if constexpr (debugOutput)
		std::cout << fmt::format(
			"\tBlock {} (junk={}, stackIn={})\n", _blockId, junkCanBeAdded, stackToString(currentStackData, m_cfg));

	auto const& blockLiveIn = m_liveness.liveIn(_blockId);
	auto const& blockLiveOut = m_liveness.liveOut(_blockId);
	auto variablesUsed = m_liveness.used(_blockId);

	SSACFG::BasicBlock const& block = m_cfg.block(_blockId);

	auto const& operationsLiveOut = m_liveness.operationsLiveOut(_blockId);
	m_stackLayout[_blockId].operationIn.reserve(block.operations.size());
	for (size_t operationIndex = 0; operationIndex < block.operations.size(); ++operationIndex)
	{
		SSACFG::Operation const& operation = block.operations[operationIndex];
		SSACFGLiveness::LivenessData opLiveOut = operationsLiveOut[operationIndex];

		if constexpr(debugOutput)
		{
			std::string const operationName = std::visit(util::GenericVisitor(
				[](SSACFG::Call const& _call) { return _call.function.get().name.str(); },
				[](SSACFG::BuiltinCall const& _call) { return _call.builtin.get().name; },
				[](SSACFG::LiteralAssignment const&) -> std::string { return "assign"; }
			), operation.kind);
			std::cout << "\t\t" << operationName << "(" << stackToString(currentStackData, m_cfg) << " -> ";
		}

		// literals should have been pulled out a priori and now are treated as push constants
		// todo yulAssert(ranges::none_of(opLiveOut, IsSSACFGLiteral(m_cfg)));
		std::set<Slot> liveOutWithoutOutputsSet;
		for (const auto& valueId: opLiveOut | ranges::views::keys)
			liveOutWithoutOutputsSet.insert(valueId);
		liveOutWithoutOutputsSet -= operation.outputs;
		auto const liveOutWithoutOutputs = std::vector<Slot>(liveOutWithoutOutputsSet.begin(), liveOutWithoutOutputsSet.end());
		std::vector<Slot> requiredStackTop;
		if (auto const* call = std::get_if<SSACFG::Call>(&operation.kind))
			if (call->canContinue)
				requiredStackTop.emplace_back(FunctionReturnLabel{&call->call.get()});
		requiredStackTop += operation.inputs;

		static auto constexpr slotIsCompatible = [](Slot const& _source, Slot const& _target)
		{
			return std::holds_alternative<JunkSlot>(_target) || _source == _target;
		};
		/*auto const fun = [&](Slot const& _slot) -> bool
		{
			if (auto const* valueId = std::get_if<SSACFG::ValueId>(&_slot))
				return !liveOutWithoutOutputsSet.contains(*valueId);
			return false;
		};*/
		// auto tail = _stack.data();

		if (!m_junkBlockFinder.blockAllowsAdditionOfJunk(_blockId))
		{
			if constexpr(debugOutput)
				std::cout << "{ " << stackToString(std::vector(liveOutWithoutOutputs.begin(), liveOutWithoutOutputs.end()), m_cfg) << " } + " << stackToString(requiredStackTop, m_cfg) << ")\n";
			DanielShuffler<StackType>::shuffle(stack, liveOutWithoutOutputsSet, requiredStackTop);
		}
		else
		{
			if constexpr(debugOutput)
				std::cout << "{ " << stackToString(pileOfJunk<Slot>(junkTailSize(stack.data())), m_cfg) << " } + " << stackToString(requiredStackTop, m_cfg) << ")\n";
			auto const v = stack.data() | ranges::views::transform([&](auto const& _slot) -> Slot { return liveOutWithoutOutputsSet.contains(_slot) ? _slot : JunkSlot{}; }) | ranges::to<std::vector<Slot>>;
			DanielShuffler<StackType>::shuffle(stack, {}, v + requiredStackTop);
		}

		m_stackLayout[_blockId].operationIn.push_back(currentStackData);

		for (size_t i = 0; i < requiredStackTop.size(); ++i)
			stack.pop();
		for (auto const& val: operation.outputs)
			stack.push(val);
	}

	// todo for conditional jump exits, we might want to change the current stack data to something that is more easily
	//		digestible for zero and nonZero branches.
	//		This might be achieved by just trying it out and counting ops.

	m_stackLayout[_blockId].stackOut = currentStackData;
	m_blockIsGenerated[_blockId.value] = true;
}
