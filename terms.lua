-- provide ways to construct all terms
-- checker untyped term and typechecking context -> typed term
-- evaluator takes typed term and runtime context -> value

-- type checker monad
-- error handling and metavariable unification facilities
--
-- typechecker is allowed to fail, typechecker monad carries failures upwards
--   for now fail fast, but design should vaguely support multiple failures

local fibbuf = require "fibonacci-buffer"

local gen = require "terms-generators"
local derivers = require "derivers"

local format = require "format"

local map = gen.declare_map
local array = gen.declare_array
local set = gen.declare_set

---@module "types.checkable"
local checkable_term = gen.declare_type()
---@module "types.inferrable"
local inferrable_term = gen.declare_type()
---@module "types.typed"
local typed_term = gen.declare_type()
---@module "types.free"
local free = gen.declare_type()
---@module "types.placeholder"
local placeholder_debug = gen.declare_type()
---@module "types.value"
local value = gen.declare_type()
---@module "types.neutral_value"
local neutral_value = gen.declare_type()
---@module "types.binding"
local binding = gen.declare_type()
---@module "types.expression_goal"
local expression_goal = gen.declare_type()

local runtime_context_mt

---@class Metavariable
---@field value integer a unique key that denotes this metavariable in the graph
---@field usage integer a unique key that denotes this metavariable in the graph
---@field trait boolean indicates if this metavariable should be solved with trait search or biunification
---@field block_level integer this probably shouldn't be inside the metavariable
local Metavariable = {}

---@return value
function Metavariable:as_value()
	return value.neutral(neutral_value.free(free.metavariable(self)))
	--local canonical = self:get_canonical()
	--local canonical_info = getmvinfo(canonical.id, self.typechecker_state.mvs)
	--return canonical_info.bound_value or value.neutral(neutral_value.free(free.metavariable(canonical)))
end

local metavariable_mt = { __index = Metavariable }
local metavariable_type = gen.declare_foreign(gen.metatable_equality(metavariable_mt), "Metavariable")

local anchor_type = gen.declare_foreign(gen.metatable_equality(format.anchor_mt), "Anchor")

---@class RuntimeContext
---@field bindings FibonacciBuffer
local RuntimeContext = {}
function RuntimeContext:get(index)
	return self.bindings:get(index)
end

---@param v value
---@return RuntimeContext
function RuntimeContext:append(v)
	-- TODO: typecheck
	local copy = { bindings = self.bindings:append(v) }
	return setmetatable(copy, runtime_context_mt)
end

---@param index integer
---@param v value
---@return RuntimeContext
function RuntimeContext:set(index, v)
	local copy = { bindings = self.bindings:set(index, v) }
	return setmetatable(copy, runtime_context_mt)
end

---@param other RuntimeContext
---@return boolean
function RuntimeContext:eq(other)
	local omt = getmetatable(other)
	if omt ~= runtime_context_mt then
		return false
	end
	return self.bindings == other.bindings
end

runtime_context_mt = {
	__index = RuntimeContext,
	__eq = RuntimeContext.eq,
}

---@return RuntimeContext
local function runtime_context()
	return setmetatable({ bindings = fibbuf() }, runtime_context_mt)
end

local typechecking_context_mt

---@class TypecheckingContext
---@field runtime_context RuntimeContext
---@field bindings FibonacciBuffer
local TypecheckingContext = {}

---get the name of a binding in a TypecheckingContext
---@param index integer
---@return string
function TypecheckingContext:get_name(index)
	return self.bindings:get(index).name
end
function TypecheckingContext:dump_names()
	for i = 1, self:len() do
		print(i, self:get_name(i))
	end
end

---@return string
function TypecheckingContext:format_names()
	local msg = ""
	for i = 1, self:len() do
		msg = msg .. tostring(i) .. "\t" .. self:get_name(i) .. "\n"
	end
	return msg
end

---@param index integer
---@return any
function TypecheckingContext:get_type(index)
	return self.bindings:get(index).type
end

---@return RuntimeContext
function TypecheckingContext:get_runtime_context()
	return self.runtime_context
end

---@param name string
---@param type any
---@param val value?
---@param anchor Anchor?
---@return TypecheckingContext
function TypecheckingContext:append(name, type, val, anchor)
	if gen.builtin_string.value_check(name) ~= true then
		error("TypecheckingContext:append parameter 'name' must be a string")
	end
	if value.value_check(type) ~= true then
		print("type", type)
		p(type)
		for k, v in pairs(type) do
			print(k, v)
		end
		print(getmetatable(type))
		error("TypecheckingContext:append parameter 'type' must be a value")
	end
	if type:is_closure() then
		error "BUG!!!"
	end
	if val ~= nil and value.value_check(val) ~= true then
		error("TypecheckingContext:append parameter 'val' must be a value (or nil if given anchor)")
	end
	if anchor ~= nil and anchor_type.value_check(anchor) ~= true then
		error("TypecheckingContext:append parameter 'anchor' must be an anchor (or nil if given val)")
	end
	if (val and anchor) or (not val and not anchor) then
		error("TypecheckingContext:append expected either val or anchor")
	end
	local copy = {
		bindings = self.bindings:append({ name = name, type = type }),
		runtime_context = self.runtime_context:append(
			val or value.neutral(neutral_value.free(free.placeholder(self:len() + 1, placeholder_debug(name, anchor))))
		),
	}
	return setmetatable(copy, typechecking_context_mt)
end

---@return integer
function TypecheckingContext:len()
	return self.bindings:len()
end

typechecking_context_mt = {
	__index = TypecheckingContext,
	__len = TypecheckingContext.len,
}

---@return TypecheckingContext
local function typechecking_context()
	return setmetatable({ bindings = fibbuf(), runtime_context = runtime_context() }, typechecking_context_mt)
end

-- empty for now, just used to mark the table
local module_mt = {}

local runtime_context_type = gen.declare_foreign(gen.metatable_equality(runtime_context_mt), "RuntimeContext")
local typechecking_context_type =
	gen.declare_foreign(gen.metatable_equality(typechecking_context_mt), "TypecheckingContext")
local host_user_defined_id = gen.declare_foreign(function(val)
	return type(val) == "table" and type(val.name) == "string"
end, "{ name: string }")

-- implicit arguments are filled in through unification
-- e.g. fn append(t : star(0), n : nat, xs : Array(t, n), val : t) -> Array(t, n+1)
--      t and n can be implicit, given the explicit argument xs, as they're filled in by unification
---@module "types.visibility"
local visibility = gen.declare_enum("visibility", {
	{ "explicit" },
	{ "implicit" },
})

expression_goal:define_enum("expression_goal", {
	-- infer
	{ "infer" },
	-- check to a goal type
	{ "check", { "goal_type", value } },
	-- TODO
	{ "mechanism", { "TODO", value } },
})

-- terms that don't have a body yet
-- stylua: ignore
binding:define_enum("binding", {
	{ "let", {
		"name", gen.builtin_string,
		"expr", inferrable_term,
	} },
	{ "tuple_elim", {
		"names",   array(gen.builtin_string),
		"subject", inferrable_term,
	} },
	{ "annotated_lambda", {
		"param_name",       gen.builtin_string,
		"param_annotation", inferrable_term,
		"anchor",           anchor_type,
		"visible",          visibility,
	} },
	{ "program_sequence", {
		"first",  inferrable_term,
		"anchor", anchor_type,
	} },
})

-- checkable terms need a goal type to typecheck against
-- stylua: ignore
checkable_term:define_enum("checkable", {
	{ "inferrable", { "inferrable_term", inferrable_term } },
	{ "tuple_cons", { "elements", array(checkable_term) } },
	{ "host_tuple_cons", { "elements", array(checkable_term) } },
	{ "lambda", {
		"param_name", gen.builtin_string,
		"body",       checkable_term,
	} },
})
-- inferrable terms can have their type inferred / don't need a goal type
-- stylua: ignore
inferrable_term:define_enum("inferrable", {
	{ "bound_variable", { "index", gen.builtin_number } },
	{ "typed", {
		"type",         value,
		"usage_counts", array(gen.builtin_number),
		"typed_term",   typed_term,
	} },
	{ "annotated_lambda", {
		"param_name",       gen.builtin_string,
		"param_annotation", inferrable_term,
		"body",             inferrable_term,
		"anchor",           anchor_type,
		"visible",          visibility,
	} },
	{ "pi", {
		"param_type",  inferrable_term,
		"param_info",  checkable_term,
		"result_type", inferrable_term,
		"result_info", checkable_term,
	} },
	{ "application", {
		"f",   inferrable_term,
		"arg", checkable_term,
	} },
	{ "tuple_cons", { "elements", array(inferrable_term) } },
	{ "tuple_elim", {
		"names",   array(gen.builtin_string),
		"subject", inferrable_term,
		"body",    inferrable_term,
	} },
	{ "tuple_type", { "desc", inferrable_term } },
	{ "record_cons", { "fields", map(gen.builtin_string, inferrable_term) } },
	{ "record_elim", {
		"subject",     inferrable_term,
		"field_names", array(gen.builtin_string),
		"body",        inferrable_term,
	} },
	{ "enum_cons", {
		"enum_type",   value,
		"constructor", gen.builtin_string,
		"arg",         inferrable_term,
	} },
	{ "enum_elim", {
		"subject",   inferrable_term,
		"mechanism", inferrable_term,
	} },
	{ "enum_type", { "desc", inferrable_term } },
	{ "object_cons", { "methods", map(gen.builtin_string, inferrable_term) } },
	{ "object_elim", {
		"subject",   inferrable_term,
		"mechanism", inferrable_term,
	} },
	{ "let", {
		"name", gen.builtin_string,
		"expr", inferrable_term,
		"body", inferrable_term,
	} },
	{ "operative_cons", {
		"operative_type", inferrable_term,
		"userdata",       inferrable_term,
	} },
	{ "operative_type_cons", {
		"handler",       checkable_term,
		"userdata_type", inferrable_term,
	} },
	{ "level_type" },
	{ "level0" },
	{ "level_suc", { "previous_level", inferrable_term } },
	{ "level_max", {
		"level_a", inferrable_term,
		"level_b", inferrable_term,
	} },
	--{"star"},
	--{"prop"},
	--{"prim"},
	{ "annotated", {
		"annotated_term", checkable_term,
		"annotated_type", inferrable_term,
	} },
	{ "host_tuple_cons", { "elements", array(inferrable_term) } }, -- host_value
	{ "host_user_defined_type_cons", {
		"id",          host_user_defined_id, -- host_user_defined_type
		"family_args", array(inferrable_term), -- host_value
	} },
	{ "host_tuple_type", { "desc", inferrable_term } }, -- just like an ordinary tuple type but can only hold host_values
	{ "host_function_type", {
		"param_type",  inferrable_term, -- must be a host_tuple_type
		-- host functions can only have explicit arguments
		"result_type", inferrable_term, -- must be a host_tuple_type
		"result_info", checkable_term,
	} },
	{ "host_wrapped_type", { "type", inferrable_term } },
	{ "host_unstrict_wrapped_type", { "type", inferrable_term } },
	{ "host_wrap", { "content", inferrable_term } },
	{ "host_unstrict_wrap", { "content", inferrable_term } },
	{ "host_unwrap", { "container", inferrable_term } },
	{ "host_unstrict_unwrap", { "container", inferrable_term } },
	{ "host_if", {
		"subject",    checkable_term, -- checkable because we always know must be of host_bool_type
		"consequent", inferrable_term,
		"alternate",  inferrable_term,
	} },
	{ "host_intrinsic", {
		"source", checkable_term,
		"type",   inferrable_term, --checkable_term,
		"anchor", anchor_type,
	} },
	{ "program_sequence", {
		"first",    inferrable_term,
		"anchor",   anchor_type,
		"continue", inferrable_term,
	} },
	{ "program_end", { "result", inferrable_term } },
	{ "program_type", {
		"effect_type", inferrable_term,
		"result_type", inferrable_term,
	} },
})

---@class SubtypeRelation
---@field debug_name string
---@field Rel value -- : (a:T,b:T) -> Prop__
---@field refl value -- : (a:T) -> Rel(a,a)
---@field antisym value -- : (a:T, B:T, Rel(a,b), Rel(b,a)) -> a == b
---@field constrain value -- : (Node(T), Node(T)) -> [TCState] ()
local subtype_relation_mt = {}

local SubtypeRelation = gen.declare_foreign(gen.metatable_equality(subtype_relation_mt), "SubtypeRelation")

local constraintelem = gen.declare_enum("constraintelem", {
	{ "sliced_constrain", {
		"rel",
		SubtypeRelation,
		"right",
		typed_term,
		"cause",
		gen.any_lua_type,
	} },
	{ "constrain_sliced", {
		"left",
		typed_term,
		"rel",
		SubtypeRelation,
		"cause",
		gen.any_lua_type,
	} },
	{
		"sliced_leftcall",
		{
			"arg",
			typed_term,
			"rel",
			SubtypeRelation,
			"right",
			typed_term,
			"cause",
			gen.any_lua_type,
		},
	},
	{
		"leftcall_sliced",
		{
			"left",
			typed_term,
			"arg",
			typed_term,
			"rel",
			SubtypeRelation,
			"cause",
			gen.any_lua_type,
		},
	},
	{
		"sliced_rightcall",
		{
			"rel",
			SubtypeRelation,
			"right",
			typed_term,
			"arg",
			typed_term,
			"cause",
			gen.any_lua_type,
		},
	},
	{
		"rightcall_sliced",
		{
			"left",
			typed_term,
			"rel",
			SubtypeRelation,
			"arg",
			typed_term,
			"cause",
			gen.any_lua_type,
		},
	},
})

-- typed terms have been typechecked but do not store their type internally
-- stylua: ignore
typed_term:define_enum("typed", {
	{ "bound_variable", { "index", gen.builtin_number } },
	{ "literal", { "literal_value", value } },
	{ "lambda", {
		"param_name", gen.builtin_string,
		"body",       typed_term,
	} },
	{ "pi", {
		"param_type",  typed_term,
		"param_info",  typed_term,
		"result_type", typed_term,
		"result_info", typed_term,
	} },
	{ "application", {
		"f",   typed_term,
		"arg", typed_term,
	} },
	{ "let", {
		"name", gen.builtin_string,
		"expr", typed_term,
		"body", typed_term,
	} },
	{ "level_type" },
	{ "level0" },
	{ "level_suc", { "previous_level", typed_term } },
	{ "level_max", {
		"level_a", typed_term,
		"level_b", typed_term,
	} },
	{ "star", { "level", gen.builtin_number } },
	{ "prop", { "level", gen.builtin_number } },
	{ "tuple_cons", { "elements", array(typed_term) } },
	--{"tuple_extend", {"base", typed_term, "fields", array(typed_term)}}, -- maybe?
	{ "tuple_elim", {
		"names",   array(gen.builtin_string),
		"subject", typed_term,
		"length",  gen.builtin_number,
		"body",    typed_term,
	} },
	{ "tuple_element_access", {
		"subject", typed_term,
		"index",   gen.builtin_number,
	} },
	{ "tuple_type", { "desc", typed_term } },
	{ "record_cons", { "fields", map(gen.builtin_string, typed_term) } },
	{ "record_extend", {
		"base",   typed_term,
		"fields", map(gen.builtin_string, typed_term),
	} },
	{ "record_elim", {
		"subject",     typed_term,
		"field_names", array(gen.builtin_string),
		"body",        typed_term,
	} },
	--TODO record elim
	{ "enum_cons", {
		"constructor", gen.builtin_string,
		"arg",         typed_term,
	} },
	{ "enum_elim", {
		"subject",   typed_term,
		"mechanism", typed_term,
	} },
	{ "enum_rec_elim", {
		"subject",   typed_term,
		"mechanism", typed_term,
	} },
	{ "enum_desc_cons", {
		"variants", map(gen.builtin_string, typed_term),
		"rest", typed_term
	} },
	{ "enum_type", {
		"desc", typed_term
	}},
	{ "enum_case", {
		"target", typed_term,
		"variants", map(gen.builtin_string, typed_term),
		"default", typed_term
	}},
	{ "enum_absurd", {
		"target", typed_term,
		"debug", gen.builtin_string
	}},
	{ "object_cons", { "methods", map(gen.builtin_string, typed_term) } },
	{ "object_corec_cons", { "methods", map(gen.builtin_string, typed_term) } },
	{ "object_elim", {
		"subject",   typed_term,
		"mechanism", typed_term,
	} },
	{ "operative_cons", { "userdata", typed_term } },
	{ "operative_type_cons", {
		"handler",       typed_term,
		"userdata_type", typed_term,
	} },
	{ "host_tuple_cons", { "elements", array(typed_term) } }, -- host_value
	{ "host_user_defined_type_cons", {
		"id",          host_user_defined_id,
		"family_args", array(typed_term), -- host_value
	} },
	{ "host_tuple_type", { "desc", typed_term } }, -- just like an ordinary tuple type but can only hold host_values
	{ "host_function_type", {
		"param_type",  typed_term, -- must be a host_tuple_type
		-- host functions can only have explicit arguments
		"result_type", typed_term, -- must be a host_tuple_type
		"result_info", typed_term,
	} },
	{ "host_wrapped_type", { "type", typed_term } },
	{ "host_unstrict_wrapped_type", { "type", typed_term } },
	{ "host_wrap", { "content", typed_term } },
	{ "host_unwrap", { "container", typed_term } },
	{ "host_unstrict_wrap", { "content", typed_term } },
	{ "host_unstrict_unwrap", { "container", typed_term } },
	{ "host_user_defined_type", {
		"id",          host_user_defined_id,
		"family_args", array(typed_term),
	} },
	{ "host_if", {
		"subject",    typed_term,
		"consequent", typed_term,
		"alternate",  typed_term,
	} },
	{ "host_intrinsic", {
		"source", typed_term,
		"anchor", anchor_type,
	} },

	-- a list of upper and lower bounds, and a relation being bound with respect to
	{ "range", {
		  "lower_bounds", array(typed_term),
		  "upper_bounds", array(typed_term),
		  "relation",     typed_term, -- a subtyping relation. not currently represented.
	} },

	{ "singleton", {
		  "supertype", typed_term,
		  "value",     value,
	} },

	{ "program_sequence", {
		"first",    typed_term,
		"continue", typed_term,
	} },
	{ "program_end", { "result", typed_term } },
	{ "program_invoke", {
		"effect_tag", typed_term,
		"effect_arg", typed_term,
	} },
	{ "effect_type", {
		"components", array(typed_term),
		"base",       typed_term,
	} },
	{ "program_type", {
		"effect_type", typed_term,
		"result_type", typed_term,
	} },
	{ "srel_type", {
		"target_type", typed_term,
	} },
	{ "variance_type", {
		"target_type", typed_term,
	} },
	{ "variance_cons", {
		"positive", typed_term,
		"srel", typed_term
	} },
	{ "intersection_type", {
		"left", typed_term,
		"right", typed_term
	} },
	{ "union_type", {
		"left", typed_term,
		"right", typed_term
	} },
	{ "constrained_type", {
		"constraints", array(constraintelem)
	}}
}) 

local unique_id = gen.builtin_table

-- stylua: ignore
placeholder_debug:define_record("placeholder_debug", {
	"name",   gen.builtin_string,
	"anchor", anchor_type,
})

-- stylua: ignore
free:define_enum("free", {
	{ "metavariable", { "metavariable", metavariable_type } },
	{ "placeholder", {
		"index", gen.builtin_number,
		"debug", placeholder_debug,
	} },
	{ "unique", { "id", unique_id } },
	-- TODO: axiom
})

-- whether a function is effectful or pure
-- an effectful function must return a monad
-- calling an effectful function implicitly inserts a monad bind between the
-- function return and getting the result of the call
---@module "types.purity"
local purity = gen.declare_enum("purity", {
	{ "effectful" },
	{ "pure" },
})

---@module 'types.block_purity'
local block_purity = gen.declare_enum("block_purity", {
	{ "effectful" },
	{ "pure" },
	{ "dependent", { "val", value } },
	{ "inherit" },
})

---@module "types.result_info"
local result_info = gen.declare_record("result_info", { "purity", purity })

---@class Registry
---@field idx integer
---@field name string
local Registry = {}

---add an entry to the registry, retrieving a unique identifier for it.
---@param name string
---@param debuginfo any
---@return table
function Registry:register(name, debuginfo)
	return {
		name = name,
		debuginfo = debuginfo,
		registry = self,
	}
end

local registry_mt = { __index = Registry }
---construct a registry for a specific kind of things
---@param name string
---@return Registry
local function new_registry(name)
	return setmetatable({ name = name }, registry_mt)
end

---@module 'types.effect_id'
local effect_id = gen.declare_type()
-- stylua: ignore
effect_id:define_record("effect_id", {
	"primary",   unique_id,
	"extension", set(unique_id), --TODO: switch to a set
})

local semantic_id = gen.declare_type()
-- stylua: ignore
semantic_id:define_record("semantic_id", {
	"primary",   unique_id,
	"extension", set(unique_id), --TODO: switch to a set
})

--TODO: consider switching to a nicer coterm representation
---@module 'types.continuation'
local continuation = gen.declare_type()
-- stylua: ignore
continuation:define_enum("continuation", {
	{ "empty" },
	{ "frame", {
		"context", runtime_context_type,
		"code",    typed_term,
	} },
	{ "sequence", {
		"first",  continuation,
		"second", continuation,
	} },
})

-- values must always be constructed in their simplest form, that cannot be reduced further.
-- their format must enforce this invariant.
-- e.g. it must be impossible to construct "2 + 2"; it should be constructed in reduced form "4".
-- values can contain neutral values, which represent free variables and stuck operations.
-- stuck operations are those that are blocked from further evaluation by a neutral value.
-- therefore neutral values must always contain another neutral value or a free variable.
-- their format must enforce this invariant.
-- e.g. it's possible to construct the neutral value "x + 2"; "2" is not neutral, but "x" is.
-- values must all be finite in size and must not have loops.
-- i.e. destructuring values always (eventually) terminates.
-- stylua: ignore
value:define_enum("value", {
	-- explicit, implicit,
	{ "visibility_type" },
	{ "visibility", { "visibility", visibility } },
	-- info about the parameter (is it implicit / what are the usage restrictions?)
	-- quantity/visibility should be restricted to free or (quantity/visibility) rather than any value
	{ "param_info_type" },
	{ "param_info", { "visibility", value } },
	-- whether or not a function is effectful /
	-- for a function returning a monad do i have to be called in an effectful context or am i pure
	{ "result_info_type" },
	{ "result_info", { "result_info", result_info } },
	{ "pi", {
		"param_type",  value,
		"param_info",  value, -- param_info
		"result_type", value, -- closure from input -> result
		"result_info", value, -- result_info
	} },
	-- closure is a type that contains a typed term corresponding to the body
	-- and a runtime context representng the bound context where the closure was created
	{ "closure", {
		"param_name", gen.builtin_string,
		"code",       typed_term,
		"capture",    runtime_context_type,
	} },

	-- a list of upper and lower bounds, and a relation being bound with respect to
	{ "range", {
		  "lower_bounds", array(value),
		  "upper_bounds", array(value),
		  "relation",     value, -- a subtyping relation. not currently represented.
	} },

	-- metaprogramming stuff
	-- TODO: add types of terms, and type indices
	-- NOTE: we're doing this through host_values instead
	--{"syntax_value", {"syntax", metalang.constructed_syntax_type}},
	--{"syntax_type"},
	--{"matcher_value", {"matcher", metalang.matcher_type}},
	--{"matcher_type", {"result_type", value}},
	--{"reducer_value", {"reducer", metalang.reducer_type}},
	--{"environment_value", {"environment", environment_type}},
	--{"environment_type"},
	--{"checkable_term", {"checkable_term", checkable_term}},
	--{"inferrable_term", {"inferrable_term", inferrable_term}},
	--{"inferrable_term_type"},
	--{"typed_term", {"typed_term", typed_term}},
	--{"typechecker_monad_value", }, -- TODO
	--{"typechecker_monad_type", {"wrapped_type", value}},
	{ "name_type" },
	{ "name", { "name", gen.builtin_string } },
	{ "operative_value", { "userdata", value } },
	{ "operative_type", {
		"handler",       value,
		"userdata_type", value,
	} },

	-- ordinary data
	{ "tuple_value", { "elements", array(value) } },
	{ "tuple_type", { "desc", value } },
	{ "tuple_desc_type", { "universe", value } },
	{ "enum_value", {
		"constructor", gen.builtin_string,
		"arg",         value,
	} },
	{ "enum_type", { "desc", value } },
	{ "enum_desc_type", { "universe", value } },
	{ "enum_desc_value", {
		"variants", gen.declare_map(gen.builtin_string, value)
	} },
	{ "record_value", { "fields", map(gen.builtin_string, value) } },
	{ "record_type", { "desc", value } },
	{ "record_desc_type", { "universe", value } },
	{ "record_extend_stuck", {
		"base",      neutral_value,
		"extension", map(gen.builtin_string, value),
	} },
	{ "object_value", {
		"methods", map(gen.builtin_string, typed_term),
		"capture", runtime_context_type,
	} },
	{ "object_type", { "desc", value } },
	{ "level_type" },
	{ "number_type" },
	{ "number", { "number", gen.builtin_number } },
	{ "level", { "level", gen.builtin_number } },
	{ "star", { "level", gen.builtin_number } },
	{ "prop", { "level", gen.builtin_number } },
	{ "neutral", { "neutral", neutral_value } },

	-- foreign data
	{ "host_value", { "host_value", gen.any_lua_type } },
	{ "host_type_type" },
	{ "host_number_type" },
	{ "host_bool_type" },
	{ "host_string_type" },
	{ "host_function_type", {
		"param_type",  value, -- must be a host_tuple_type
		-- host functions can only have explicit arguments
		"result_type", value, -- must be a host_tuple_type
		"result_info", value,
	} },
	{ "host_wrapped_type", { "type", value } },
	{ "host_unstrict_wrapped_type", { "type", value } },
	{ "host_user_defined_type", {
		"id",          host_user_defined_id,
		"family_args", array(value),
	} },
	{ "host_nil_type" },
	--NOTE: host_tuple is not considered a host type because it's not a first class value in lua.
	{ "host_tuple_value", { "elements", array(gen.any_lua_type) } },
	{ "host_tuple_type", { "desc", value } }, -- just like an ordinary tuple type but can only hold host_values

	-- type of key and value of key -> type of the value
	-- {"host_table_type"},

	-- a type family, that takes a type and a value, and produces a new type
	-- inhabited only by that single value and is a subtype of the type.
	-- example: singleton(integer, 5) is the type that is inhabited only by the
	-- number 5. values of this type can be, for example, passed to a function
	-- that takes any integer.
	-- alternative names include:
	-- - Most Specific Type (from discussion with open),
	-- - Val (from julia)
	{ "singleton", {
		"supertype", value,
		"value",     value,
	} },
	{ "program_end", { "result", value } },
	{ "program_cont", {
		"action",       unique_id,
		"argument",     value,
		"continuation", continuation,
	} },
	{ "effect_empty" },
	{ "effect_elem", { "tag", effect_id } },
	{ "effect_type" },
	{ "effect_row", {
		"components", set(unique_id),
		"rest",       value,
	} },
	{ "effect_row_type" },
	{ "program_type", {
		"effect_sig", value,
		"base_type",  value,
	} },
	{ "srel_type", {
		"target_type", value,
	} },
	{ "variance_type",{
		"target_type", value
	} },
	{ "intersection_type", {
		"left", value,
		"right", value
	} },
	{ "union_type", {
		"left", value,
		"right", value
	} }
})

-- stylua: ignore
neutral_value:define_enum("neutral_value", {
	-- fn(free_value) and table of functions eg free.metavariable(metavariable)
	-- value should be constructed w/ free.something()
	{ "free", { "free", free } },
	{ "application_stuck", {
		"f",   neutral_value,
		"arg", value,
	} },
	{ "enum_elim_stuck", {
		"mechanism", value,
		"subject",   neutral_value,
	} },
	{ "enum_rec_elim_stuck", {
		"handler", value,
		"subject", neutral_value,
	} },
	{ "object_elim_stuck", {
		"mechanism", value,
		"subject",   neutral_value,
	} },
	{ "tuple_element_access_stuck", {
		"subject", neutral_value,
		"index",   gen.builtin_number,
	} },
	{ "record_field_access_stuck", {
		"subject",    neutral_value,
		"field_name", gen.builtin_string,
	} },
	{ "host_application_stuck", {
		"function", gen.any_lua_type,
		"arg",      neutral_value,
	} },
	{ "host_tuple_stuck", {
		"leading",       array(gen.any_lua_type),
		"stuck_element", neutral_value,
		"trailing",      array(value), -- either host or neutral
	} },
	{ "host_if_stuck", {
		"subject",    neutral_value,
		"consequent", value,
		"alternate",  value,
	} },
	{ "host_intrinsic_stuck", {
		"source", neutral_value,
		"anchor", anchor_type,
	} },
	{ "host_wrap_stuck", { "content", neutral_value } },
	{ "host_unwrap_stuck", { "container", neutral_value } },
})

local host_syntax_type = value.host_user_defined_type({ name = "syntax" }, array(value)())
local host_environment_type = value.host_user_defined_type({ name = "environment" }, array(value)())
local host_typed_term_type = value.host_user_defined_type({ name = "typed_term" }, array(value)())
local host_goal_type = value.host_user_defined_type({ name = "goal" }, array(value)())
local host_inferrable_term_type = value.host_user_defined_type({ name = "inferrable_term" }, array(value)())
local host_checkable_term_type = value.host_user_defined_type({ name = "checkable_term" }, array(value)())
-- return ok, err
local host_lua_error_type = value.host_user_defined_type({ name = "lua_error_type" }, array(value)())

---@class DescConsContainer
local DescCons = --[[@enum DescCons]]
	{
		cons = "cons",
		empty = "empty",
	}

local value_array = array(value)

---@param ... value
---@return value
local function tup_val(...)
	return value.tuple_value(value_array(...))
end

---@param ... value
---@return value
local function cons(...)
	return value.enum_value(DescCons.cons, tup_val(...))
end

local empty = value.enum_value(DescCons.empty, tup_val())
local unit_type = value.tuple_type(empty)
local unit_val = tup_val()

---@param a value
---@param e value
---@param ... value
---@return value
local function tuple_desc_inner(a, e, ...)
	if e == nil then
		return a
	else
		return tuple_desc_inner(cons(a, e), ...)
	end
end

---@param ... value
---@return value
local function tuple_desc(...)
	return tuple_desc_inner(empty, ...)
end

local effect_registry = new_registry("effect")
local TCState =
	effect_id(effect_registry:register("TCState", "effects that manipulate the typechecker state"), set(unique_id)())
local lua_prog = effect_id(effect_registry:register("lua_prog", "running effectful lua code"), set(unique_id)())

local terms = {
	metavariable_mt = metavariable_mt,
	checkable_term = checkable_term, -- {}
	inferrable_term = inferrable_term, -- {}
	typed_term = typed_term, -- {}
	free = free,
	visibility = visibility,
	purity = purity,
	block_purity = block_purity,
	result_info = result_info,
	value = value,
	neutral_value = neutral_value,
	binding = binding,
	expression_goal = expression_goal,
	host_syntax_type = host_syntax_type,
	host_environment_type = host_environment_type,
	host_typed_term_type = host_typed_term_type,
	host_goal_type = host_goal_type,
	host_inferrable_term_type = host_inferrable_term_type,
	host_checkable_term_type = host_checkable_term_type,
	host_lua_error_type = host_lua_error_type,
	unique_id = unique_id,

	runtime_context = runtime_context,
	typechecking_context = typechecking_context,
	module_mt = module_mt,
	runtime_context_type = runtime_context_type,
	typechecking_context_type = typechecking_context_type,
	subtype_relation_mt = subtype_relation_mt,
	SubtypeRelation = SubtypeRelation,
	constraintelem = constraintelem,

	DescCons = DescCons,
	tup_val = tup_val,
	cons = cons,
	empty = empty,
	tuple_desc = tuple_desc,
	unit_type = unit_type,
	unit_val = unit_val,
	effect_id = effect_id,
	continuation = continuation,

	effect_registry = effect_registry,
	TCState = TCState,
	lua_prog = lua_prog,
}

local override_prettys = require "terms-pretty"(terms)
local checkable_term_override_pretty = override_prettys.checkable_term_override_pretty
local inferrable_term_override_pretty = override_prettys.inferrable_term_override_pretty
local typed_term_override_pretty = override_prettys.typed_term_override_pretty
local value_override_pretty = override_prettys.value_override_pretty
local binding_override_pretty = override_prettys.binding_override_pretty

checkable_term:derive(derivers.pretty_print, checkable_term_override_pretty)
inferrable_term:derive(derivers.pretty_print, inferrable_term_override_pretty)
typed_term:derive(derivers.pretty_print, typed_term_override_pretty)
visibility:derive(derivers.pretty_print)
free:derive(derivers.pretty_print)
value:derive(derivers.pretty_print, value_override_pretty)
neutral_value:derive(derivers.pretty_print)
binding:derive(derivers.pretty_print, binding_override_pretty)
expression_goal:derive(derivers.pretty_print)
placeholder_debug:derive(derivers.pretty_print)
purity:derive(derivers.pretty_print)
result_info:derive(derivers.pretty_print)

local internals_interface = require "internals-interface"
internals_interface.terms = terms
return terms
