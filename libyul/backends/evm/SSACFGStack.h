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

#include "SSAControlFlowGraph.h"


#include <libyul/Exceptions.h>

#include <libsolutil/CommonData.h>

#include <range/v3/range.hpp>
#include <range/v3/view/reverse.hpp>

#include <concepts>
#include <optional>

namespace solidity::yul::ssa
{

template<typename StackData>
concept StackDataConcept = requires(StackData _stackData, typename StackData::Slot _stackSlot, size_t _depth)
{
	typename StackData::Slot;

	{ ranges::range<ranges::range_value_t<StackData>> };
	{ ranges::range_value_t<StackData>{} } -> std::convertible_to<typename StackData::Slot>;

	{ _stackData.slots } -> std::same_as<std::vector<typename StackData::Slot>&>;
};

template<typename StackManipulationOps, typename Data>
concept StackManipulationOpsConcept = requires(
	StackManipulationOps _ops,
	typename StackManipulationOps::StackData::Slot _slot,
	Data& _data,
	size_t _depth
)
{
	typename StackManipulationOps::StackData;
	{ StackManipulationOps::canBeFreelyGenerated(_slot) } -> std::same_as<bool>;
	{ _ops.swap(_data, _depth) } -> std::same_as<void>;
	{ _ops.dup(_data, _depth) } -> std::same_as<void>;
	{ _ops.push(_data, _slot) } -> std::same_as<void>;
	{ _ops.pop(_data) } -> std::same_as<void>;
};

template<typename Data, typename Ops> requires StackDataConcept<Data> && StackManipulationOpsConcept<Ops, Data>
class SSACFGStack
{
public:
	using Slot = typename Data::Slot;

	SSACFGStack(
		Data _data,
		Ops _ops
	):
		m_data(std::move(_data)),
		m_ops(std::move(_ops))
	{}

	Slot const& top() const
	{
		yulAssert(!m_data.slots.empty());
		return m_data.slots.back();
	}

	void swap(size_t const _depth)
	{
		m_ops.swap(m_data, _depth);
		/*yulAssert(m_data.size() > _depth);
		std::swap(m_data[m_data.size() - _depth - 1], m_data.back());
		m_swap(_depth);*/
	}

	void pop()
	{
		m_ops.pop(m_data);
		/*yulAssert(!m_data.empty());
		m_data.pop_back();
		m_pop();*/
	}

	void push(Slot const& _value)
	{
		m_ops.push(m_data, _value);
		/*m_data.emplace_back(_value);
		m_push(_value);*/
	}

	void dup(Slot const& _slot)
	{
		std::optional<size_t> const depth = slotDepth(_slot);
		yulAssert(depth, "Invalid dup");
		m_ops.dup(m_data, *depth + 1);
		//m_data.push_back(m_data[m_data.size() - *depth - 1]);
		//m_dup(*depth + 1);
	}

	void pushOrDup(Slot const& _slot)
	{
		if (m_ops.canBeFreelyGenerated(_slot))
			push(_slot);
		else
			dup(_slot);
	}

	size_t size() const
	{
		return m_data.slots.size();
	}

	std::optional<size_t> slotDepth(Slot const& _value) const
	{
		return util::findOffset(m_data.slots | ranges::views::reverse, _value);
	}

	Slot const& operator[](size_t const _index) const { return m_data[_index]; }
	auto begin() const { return ranges::begin(m_data); }
	auto end() const { return ranges::end(m_data); }

private:
	Data m_data;
	Ops m_ops;
};

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

struct StackData
{
	using Slot = std::variant<SSACFG::ValueId, AbstractAssembly::LabelID, FunctionReturnLabel, JunkSlot>;

	auto begin() const { return ranges::begin(slots); }
	auto end() const { return ranges::end(slots); }

	std::vector<Slot> slots;
};
static_assert(StackDataConcept<StackData>);

struct ManipulationOps
{
	using Slot = StackData::Slot;
	static bool canBeFreelyGenerated(Slot const& _slot) {
		return std::holds_alternative<JunkSlot>(_slot) || ; // todo maybe literal up to certain size?
	}
};

}
