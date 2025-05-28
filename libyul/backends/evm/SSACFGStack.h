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

#include <libyul/backends/evm/SSAControlFlowGraph.h>

#include <libyul/Exceptions.h>

#include <libsolutil/CommonData.h>
#include <libsolutil/Visitor.h>

#include <range/v3/algorithm/count_if.hpp>
#include <range/v3/view/reverse.hpp>
#include <range/v3/range.hpp>

#include <fmt/ranges.h>

#include <concepts>
#include <optional>
#include <variant>

namespace solidity::yul::ssa
{

struct FunctionReturnLabel
{
	FunctionCall const* functionCall;
	auto operator<=>(FunctionReturnLabel const&) const = default;
};

struct JunkSlot
{
	bool operator==(JunkSlot const&) const { return true; }
	bool operator<(JunkSlot const&) const { return false; }
};

using StackSlot = std::variant<AbstractAssembly::LabelID, SSACFG::ValueId, FunctionReturnLabel, JunkSlot>;
using StackData = std::vector<StackSlot>;

template<typename StackManipulationCallback>
concept StackManipulationCallbackConcept = requires(
	StackManipulationCallback _callback,
	StackSlot _slot,
	size_t _depth
)
{
	{ _callback.swap(_depth) } -> std::same_as<void>;
	{ _callback.dup(_depth) } -> std::same_as<void>;
	{ _callback.push(_slot) } -> std::same_as<void>;
	{ _callback.pop() } -> std::same_as<void>;
};

struct NoOpStackManipulationCallbacks
{
	static void swap(size_t) {}
	static void dup(size_t) {}
	static void push(StackSlot const&) {}
	static void pop() {}
};
static_assert(StackManipulationCallbackConcept<NoOpStackManipulationCallbacks>);


static std::string slotToString(StackSlot const& _slot, SSACFG const& _cfg)
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


static std::string stackToString(StackData const& _stackData, SSACFG const& _cfg)
{
	return format(
		"[{}]",
		fmt::join(_stackData | ranges::views::transform([&](auto const& _slot) { return slotToString(_slot, _cfg); }), ", ")
	);
}

template<StackManipulationCallbackConcept Callbacks = NoOpStackManipulationCallbacks>
class Stack
{
public:
	using Slot = StackSlot;
	using Data = std::vector<Slot>;

	Stack(
		StackData _data,
		Callbacks _callbacks,
		SSACFG const& _cfg
	):
		m_cfg(&_cfg),
		m_data(std::move(_data)),
		m_callbacks(std::move(_callbacks))
	{}

	Slot const& top() const
	{
		yulAssert(!m_data.empty());
		return m_data.back();
	}

	void swap(size_t const _depth)
	{
		yulAssert(m_data.size() > _depth);
		std::swap(m_data[m_data.size() - _depth - 1], m_data.back());
		if constexpr (!std::is_same_v<Callbacks, NoOpStackManipulationCallbacks>)
			m_callbacks.swap(_depth);
	}

	template<bool callback=true>
	void pop()
	{
		yulAssert(!m_data.empty());
		m_data.pop_back();
		if constexpr (callback && !std::is_same_v<Callbacks, NoOpStackManipulationCallbacks>)
			m_callbacks.pop();
	}

	template<bool callback=true>
	void push(Slot const& _slot)
	{
		m_data.emplace_back(_slot);
		if constexpr (callback && !std::is_same_v<Callbacks, NoOpStackManipulationCallbacks>)
			m_callbacks.push(_slot);
	}

	void dup(Slot const& _slot)
	{
		std::optional<size_t> const depth = slotDepth(_slot);
		yulAssert(depth, fmt::format("Invalid dup, could not find slot {}", slotToString(_slot, *m_cfg)));
		m_data.push_back(m_data[m_data.size() - *depth - 1]);
		if constexpr (!std::is_same_v<Callbacks, NoOpStackManipulationCallbacks>)
			m_callbacks.dup(*depth + 1);
	}

	void pushOrDup(Slot const& _slot)
	{
		if (canBeFreelyGenerated(_slot))
			push(_slot);
		else
			dup(_slot);
	}

	size_t size() const
	{
		return m_data.size();
	}

	std::optional<size_t> slotDepth(Slot const& _value) const
	{
		return util::findOffset(m_data | ranges::views::reverse, _value);
	}

	bool canBeFreelyGenerated(Slot const& _slot) const
	{
		if (std::holds_alternative<JunkSlot>(_slot))
			return true;
		if (std::holds_alternative<FunctionReturnLabel>(_slot))
			return true;
		if (std::holds_alternative<SSACFG::ValueId>(_slot))
			return m_cfg->isLiteralValue(std::get<SSACFG::ValueId>(_slot));
		return false;
	}

	Slot const& operator[](size_t const _index) const { return m_data[_index]; }
	auto begin() const { return ranges::begin(m_data); }
	auto end() const { return ranges::end(m_data); }

	size_t numJunkSlots() const
	{
		return static_cast<size_t>(ranges::count_if(m_data, [](Slot const& _slot) { return std::holds_alternative<JunkSlot>(_slot); } ));
	}

	void addJunkTail(std::ptrdiff_t const _numJunk)
	{
		yulAssert(_numJunk >= 0);
		if (_numJunk == 0)
			return;

		// append junk (so it's at the stack top)
		m_data.resize(m_data.size() + static_cast<std::size_t>(_numJunk));
		std::fill_n(m_data.rbegin(), static_cast<std::size_t>(_numJunk), JunkSlot{});
		// rotate to the right by numJunk elements, now they're in the tail
		std::rotate(m_data.rbegin(), m_data.rbegin() + static_cast<std::ptrdiff_t>(_numJunk), m_data.rend());
	}

	std::string str() const
	{
		return stackToString(m_data, *m_cfg);
	}

	StackData const& data() const
	{
		return m_data;
	}

private:
	SSACFG const* m_cfg;
	StackData m_data;
	Callbacks m_callbacks;
};

}
