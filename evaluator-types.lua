-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

local gen = require "terms-generators"
local derivers = require "derivers"
local terms = require "terms"

local flex_value = terms.flex_value

---@module "types.edgenotif"
local EdgeNotif = gen.declare_type()

local SubtypeRelation = terms.SubtypeRelation

-- stylua: ignore
EdgeNotif:define_enum("edgenotif", {
	{ "Constrain", {
		"left",  gen.builtin_integer,
		"rel",  SubtypeRelation,
		"right", gen.builtin_integer,
		"shallowest_block", gen.builtin_integer,
		"cause",  terms.constraintcause,
	} },
	{ "CallLeft", {
		"left",  gen.builtin_integer,
		"arg",  flex_value,
		"rel",  SubtypeRelation,
		"right", gen.builtin_integer,
		"shallowest_block", gen.builtin_integer,
		"cause",  terms.constraintcause,
	} },
	{ "CallRight", {
		"left",  gen.builtin_integer,
		"rel",  SubtypeRelation,
		"right", gen.builtin_integer,
		"arg",  flex_value,
		"shallowest_block", gen.builtin_integer,
		"cause",  terms.constraintcause,
	} },
}
)

EdgeNotif:derive(derivers.pretty_print)

return { subtype_relation_mt = terms.subtype_relation_mt, SubtypeRelation = SubtypeRelation, EdgeNotif = EdgeNotif }
