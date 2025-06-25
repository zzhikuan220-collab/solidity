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
#include <libyul/backends/evm/SSAControlFlowGraph.h>

#include <libyul/Exceptions.h>

#include <libsolutil/CommonData.h>

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

template<typename CanBeFreelyGenerated, typename Slot>
concept CanBeFreelyGeneratedConcept = requires(
	CanBeFreelyGenerated _canBeFreelyGenerated,
	Slot _slot
)
{
	{ _canBeFreelyGenerated(_slot) } -> std::same_as<bool>;
};

template<typename SlotType>
struct SlotCanBeFreelyGenerated
{
	using Slot = SlotType;
	bool operator()(Slot const& _slot) const
	{
		if (std::holds_alternative<SSACFG::ValueId>(_slot))
			return m_cfg->isLiteralValue(std::get<SSACFG::ValueId>(_slot));
		return std::holds_alternative<JunkSlot>(_slot) || std::holds_alternative<FunctionReturnLabel>(_slot);
	}

	SSACFG const* m_cfg;
};
static_assert(CanBeFreelyGeneratedConcept<SlotCanBeFreelyGenerated<StackSlot>, StackSlot>);

template<typename StackManipulationCallback, typename Slot>
concept StackManipulationCallbackConcept = requires(
	StackManipulationCallback& _callback,
	Slot _slot,
	size_t _depth
)
{
	{ _callback.swap(_depth) } -> std::same_as<void>;
	{ _callback.dup(_depth) } -> std::same_as<void>;
	{ _callback.push(_slot) } -> std::same_as<void>;
	{ _callback.pop() } -> std::same_as<void>;
};

template<typename StackSlot>
struct NoOpStackManipulationCallbacks
{
	using Slot = StackSlot;
	static void swap(size_t) {}
	static void dup(size_t) {}
	static void push(Slot const&) {}
	static void pop() {}
};
static_assert(StackManipulationCallbackConcept<NoOpStackManipulationCallbacks<StackSlot>, StackSlot>);


std::string slotToString(StackSlot const& _slot, SSACFG const& _cfg);
std::string stackToString(StackData const& _stackData, SSACFG const& _cfg);

template<
	typename StackSlot,
	StackManipulationCallbackConcept<StackSlot> Callbacks = NoOpStackManipulationCallbacks<StackSlot>,
	CanBeFreelyGeneratedConcept<StackSlot> CanBeFreelyGenerated = SlotCanBeFreelyGenerated<StackSlot>
>
class Stack
{
	static size_t constexpr reachableStackDepth = 16;
public:
	using Slot = typename Callbacks::Slot;
	using Data = std::vector<Slot>;

	Stack(
		Data _data,
		Callbacks _callbacks,
		CanBeFreelyGenerated _canBeFreelyGenerated
	):
		m_data(std::move(_data)),
		m_callbacks(std::move(_callbacks)),
		m_canBeFreelyGenerated(std::move(_canBeFreelyGenerated))
	{}

	Slot const& top() const
	{
		yulAssert(!m_data.empty());
		return m_data.back();
	}

	void swap(size_t const _depth)
	{
		yulAssert(m_data.size() > _depth);
		yulAssert(1 <= _depth && _depth <= reachableStackDepth);
		std::swap(m_data[m_data.size() - _depth - 1], m_data.back());
		if constexpr (!std::is_same_v<Callbacks, NoOpStackManipulationCallbacks<Slot>>)
			m_callbacks.swap(_depth);
	}

	template<bool callback=true>
	void pop()
	{
		yulAssert(!m_data.empty());
		m_data.pop_back();
		if constexpr (callback && !std::is_same_v<Callbacks, NoOpStackManipulationCallbacks<Slot>>)
			m_callbacks.pop();
	}

	template<bool callback=true>
	void push(Slot const& _slot)
	{
		m_data.emplace_back(_slot);
		if constexpr (callback && !std::is_same_v<Callbacks, NoOpStackManipulationCallbacks<Slot>>)
			m_callbacks.push(_slot);
	}

	void declareJunk(size_t const _depth)
	{
		yulAssert(_depth < m_data.size());
		m_data[_depth] = JunkSlot{};
	}

	void dup(Slot const& _slot)
	{
		std::optional<size_t> const depth = slotDepth(_slot);
		yulAssert(depth, fmt::format("Invalid dup, could not find slot"));
		yulAssert(1 <= *depth + 1 && *depth + 1 <= reachableStackDepth);
		m_data.push_back(m_data[m_data.size() - *depth - 1]);
		if constexpr (!std::is_same_v<Callbacks, NoOpStackManipulationCallbacks<Slot>>)
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
		return m_canBeFreelyGenerated(_slot);
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

	Data const& data() const
	{
		return m_data;
	}

private:
	Data m_data;
	Callbacks m_callbacks;
	CanBeFreelyGenerated m_canBeFreelyGenerated;
};

}
