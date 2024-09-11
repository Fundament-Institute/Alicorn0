local gen = require "terms-generators"
local derivers = require "derivers"
local terms = require "terms"

local value = terms.value

---@module "evaluator.edgenotif"
local EdgeNotif = gen.declare_type()

---@class SubtypeRelation
---@field debug_name string
---@field Rel value -- : (a:T,b:T) -> Prop__
---@field refl value -- : (a:T) -> Rel(a,a)
---@field antisym value -- : (a:T, B:T, Rel(a,b), Rel(b,a)) -> a == b
---@field constrain value -- : (Node(T), Node(T)) -> [TCState] ()
local subtype_relation_mt = {}

local SubtypeRelation = gen.declare_foreign(gen.metatable_equality(subtype_relation_mt), "SubtypeRelation")

-- stylua: ignore
EdgeNotif:define_enum("edgenotif", {
	{ "Constrain", {
		"left",  gen.builtin_number,
		"rel",  SubtypeRelation,
		"right", gen.builtin_number,
		"shallowest_block", gen.builtin_number,
		"cause",  gen.any_lua_type,
	} },
	{ "CallLeft", {
		"left",  gen.builtin_number,
		"arg",  value,
		"rel",  SubtypeRelation,
		"right", gen.builtin_number,
		"shallowest_block", gen.builtin_number,
		"cause",  gen.any_lua_type,
	} },
	{ "CallRight", {
		"left",  gen.builtin_number,
		"rel",  SubtypeRelation,
		"right", gen.builtin_number,
		"arg",  value,
		"shallowest_block", gen.builtin_number,
		"cause",  gen.any_lua_type,
	} },
}
)

EdgeNotif:derive(derivers.pretty_print)

return { subtype_relation_mt = subtype_relation_mt, SubtypeRelation = SubtypeRelation, EdgeNotif = EdgeNotif }
