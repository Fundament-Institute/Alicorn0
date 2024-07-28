-- provide ways to construct all terms
-- checker untyped term and typechecking context -> typed term
-- evaluator takes typed term and runtime context -> value

-- type checker monad
-- error handling and metavariable unification facilities
--
-- typechecker is allowed to fail, typechecker monad carries failures upwards
--   for now fail fast, but design should vaguely support multiple failures

--local metalang = require "./metalanguage"
--local types = require "./typesystem"

local fibbuf = require "./fibonacci-buffer"

local gen = require "./terms-generators"
local derivers = require "./derivers"

local map = gen.declare_map
local array = gen.declare_array

---@module "./types/checkable"
local checkable_term = gen.declare_type()
---@module "./types/inferrable"
local inferrable_term = gen.declare_type()
---@module "./types/typed"
local typed_term = gen.declare_type()
---@module "./types/free"
local free = gen.declare_type()
---@module "./types/placeholder"
local placeholder_debug = gen.declare_type()
---@module "./types/value"
local value = gen.declare_type()
---@module "./types/neutral"
local neutral_value = gen.declare_type()
---@module "./types/binding"
local binding = gen.declare_type()
---@module "./types/expression_goal"
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
local metavariable_type = gen.declare_foreign(gen.metatable_equality(metavariable_mt))

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
	for i = 1, #self do
		print(i, self:get_name(i))
	end
end

---@return string
function TypecheckingContext:format_names()
	local msg = ""
	for i = 1, #self do
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
	-- TODO: typecheck
	if name == nil or type == nil then
		error("bug!!!")
	end
	if value.value_check(type) ~= true then
		print("type", type)
		p(type)
		for k, v in pairs(type) do
			print(k, v)
		end
		print(getmetatable(type))
		error "TypecheckingContext:append type parameter of wrong type"
	end
	if type:is_closure() then
		error "BUG!!!"
	end
	local copy = {
		bindings = self.bindings:append({ name = name, type = type }),
		runtime_context = self.runtime_context:append(
			val or value.neutral(neutral_value.free(free.placeholder(#self + 1, placeholder_debug(name, anchor))))
		),
	}
	return setmetatable(copy, typechecking_context_mt)
end

typechecking_context_mt = {
	__index = TypecheckingContext,
	__len = function(self)
		return self.bindings:len()
	end,
}

---@return TypecheckingContext
local function typechecking_context()
	return setmetatable({ bindings = fibbuf(), runtime_context = runtime_context() }, typechecking_context_mt)
end

-- empty for now, just used to mark the table
local module_mt = {}

local runtime_context_type = gen.declare_foreign(gen.metatable_equality(runtime_context_mt))
local typechecking_context_type = gen.declare_foreign(gen.metatable_equality(typechecking_context_mt))
local prim_user_defined_id = gen.declare_foreign(function(val)
	return type(val) == "table" and type(val.name) == "string"
end)

-- implicit arguments are filled in through unification
-- e.g. fn append(t : star(0), n : nat, xs : Array(t, n), val : t) -> Array(t, n+1)
--      t and n can be implicit, given the explicit argument xs, as they're filled in by unification
---@module "./types/visibility"
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
		"anchor",           gen.anchor_type,
		"visible",          visibility,
	} },
})

-- checkable terms need a goal type to typecheck against
-- stylua: ignore
checkable_term:define_enum("checkable", {
	{ "inferrable", { "inferrable_term", inferrable_term } },
	{ "tuple_cons", { "elements", array(checkable_term) } },
	{ "prim_tuple_cons", { "elements", array(checkable_term) } },
	{ "lambda", {
		"param_name", gen.builtin_string,
		"body",       checkable_term,
	} },
	-- TODO: enum_cons
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
		"anchor",           gen.anchor_type,
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
	{ "tuple_type", { "definition", inferrable_term } },
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
	{ "enum_type", { "definition", inferrable_term } },
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
	{ "prim_tuple_cons", { "elements", array(inferrable_term) } }, -- prim
	{ "prim_user_defined_type_cons", {
		"id",          prim_user_defined_id, -- prim_user_defined_type
		"family_args", array(inferrable_term), -- prim
	} },
	{ "prim_tuple_type", { "decls", inferrable_term } }, -- just like an ordinary tuple type but can only hold prims
	{ "prim_function_type", {
		"param_type",  inferrable_term, -- must be a prim_tuple_type
		-- primitive functions can only have explicit arguments
		"result_type", inferrable_term, -- must be a prim_tuple_type
		-- primitive functions can only be pure for now
	} },
	{ "prim_wrapped_type", { "type", inferrable_term } },
	{ "prim_unstrict_wrapped_type", { "type", inferrable_term } },
	{ "prim_wrap", { "content", inferrable_term } },
	{ "prim_unstrict_wrap", { "content", inferrable_term } },
	{ "prim_unwrap", { "container", inferrable_term } },
	{ "prim_unstrict_unwrap", { "container", inferrable_term } },
	{ "prim_if", {
		"subject",    checkable_term, -- checkable because we always know must be of prim_bool_type
		"consequent", inferrable_term,
		"alternate",  inferrable_term,
	} },
	{ "prim_intrinsic", {
		"source", checkable_term,
		"type",   inferrable_term, --checkable_term,
		"anchor", gen.anchor_type,
	} },
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
	{ "tuple_type", { "definition", typed_term } },
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
	{ "prim_tuple_cons", { "elements", array(typed_term) } }, -- prim
	{ "prim_user_defined_type_cons", {
		"id",          prim_user_defined_id,
		"family_args", array(typed_term), -- prim
	} },
	{ "prim_tuple_type", { "decls", typed_term } }, -- just like an ordinary tuple type but can only hold prims
	{ "prim_function_type", {
		"param_type",  typed_term, -- must be a prim_tuple_type
		-- primitive functions can only have explicit arguments
		"result_type", typed_term, -- must be a prim_tuple_type
		-- primitive functions can only be pure for now
	} },
	{ "prim_wrapped_type", { "type", typed_term } },
	{ "prim_unstrict_wrapped_type", { "type", typed_term } },
	{ "prim_wrap", { "content", typed_term } },
	{ "prim_unwrap", { "container", typed_term } },
	{ "prim_unstrict_wrap", { "content", typed_term } },
	{ "prim_unstrict_unwrap", { "container", typed_term } },
	{ "prim_user_defined_type", {
		"id",          prim_user_defined_id,
		"family_args", array(typed_term),
	} },
	{ "prim_if", {
		"subject",    typed_term,
		"consequent", typed_term,
		"alternate",  typed_term,
	} },
	{ "prim_intrinsic", {
		"source", typed_term,
		"anchor", gen.anchor_type,
	} },

	-- a list of upper and lower bounds, and a relation being bound with respect to
	{ "range", {
		  "lower_bounds", array(typed_term),
		  "upper_bounds", array(typed_term),
		  "relation", typed_term -- a subtyping relation. not currently represented.
	} },


})

local unique_id = gen.declare_foreign(function(val)
	return type(val) == "table"
end)

-- stylua: ignore
placeholder_debug:define_record("placeholder_debug", {
	"name",   gen.builtin_string,
	"anchor", gen.anchor_type,
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
---@module "./types/purity"
local purity = gen.declare_enum("purity", {
	{ "effectful" },
	{ "pure" },
})

---@module "./types/result_info"
local result_info = gen.declare_record("result_info", { "purity", purity })

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
		  "relation", value -- a subtyping relation. not currently represented.
	} },

	-- metaprogramming stuff
	-- TODO: add types of terms, and type indices
	-- NOTE: we're doing this through prims instead
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
	{ "tuple_type", { "decls", value } },
	{ "tuple_defn_type", { "universe", value } },
	{ "enum_value", {
		"constructor", gen.builtin_string,
		"arg",         value,
	} },
	{ "enum_type", { "decls", value } },
	{ "enum_defn_type", { "universe", value } },
	{ "record_value", { "fields", map(gen.builtin_string, value) } },
	{ "record_type", { "decls", value } },
	{ "record_defn_type", { "universe", value } },
	{ "record_extend_stuck", {
		"base",      neutral_value,
		"extension", map(gen.builtin_string, value),
	} },
	{ "object_value", {
		"methods", map(gen.builtin_string, typed_term),
		"capture", runtime_context_type,
	} },
	{ "object_type", { "decls", value } },
	{ "level_type" },
	{ "number_type" },
	{ "number", { "number", gen.builtin_number } },
	{ "level", { "level", gen.builtin_number } },
	{ "star", { "level", gen.builtin_number } },
	{ "prop", { "level", gen.builtin_number } },
	{ "neutral", { "neutral", neutral_value } },

	-- foreign data
	{ "prim", { "primitive_value", gen.any_lua_type } },
	{ "prim_type_type" },
	{ "prim_number_type" },
	{ "prim_bool_type" },
	{ "prim_string_type" },
	{ "prim_function_type", {
		"param_type",  value, -- must be a prim_tuple_type
		-- primitive functions can only have explicit arguments
		"result_type", value, -- must be a prim_tuple_type
		-- primitive functions can only be pure for now
	} },
	{ "prim_wrapped_type", { "type", value } },
	{ "prim_unstrict_wrapped_type", { "type", value } },
	{ "prim_user_defined_type", {
		"id",          prim_user_defined_id,
		"family_args", array(value),
	} },
	{ "prim_nil_type" },
	--NOTE: prim_tuple is not considered a prim type because it's not a first class value in lua.
	{ "prim_tuple_value", { "elements", array(gen.any_lua_type) } },
	{ "prim_tuple_type", { "decls", value } }, -- just like an ordinary tuple type but can only hold prims

	-- type of key and value of key -> type of the value
	-- {"prim_table_type"},

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
	{ "prim_application_stuck", {
		"function", gen.any_lua_type,
		"arg",      neutral_value,
	} },
	{ "prim_tuple_stuck", {
		"leading",       array(gen.any_lua_type),
		"stuck_element", neutral_value,
		"trailing",      array(value), -- either primitive or neutral
	} },
	{ "prim_if_stuck", {
		"subject",    neutral_value,
		"consequent", value,
		"alternate",  value,
	} },
	{ "prim_intrinsic_stuck", {
		"source", neutral_value,
		"anchor", gen.anchor_type,
	} },
	{ "prim_wrap_stuck", { "content", neutral_value } },
	{ "prim_unwrap_stuck", { "container", neutral_value } },
})

local prim_syntax_type = value.prim_user_defined_type({ name = "syntax" }, array(value)())
local prim_environment_type = value.prim_user_defined_type({ name = "environment" }, array(value)())
local prim_typed_term_type = value.prim_user_defined_type({ name = "typed_term" }, array(value)())
local prim_goal_type = value.prim_user_defined_type({ name = "goal" }, array(value)())
local prim_inferrable_term_type = value.prim_user_defined_type({ name = "inferrable_term" }, array(value)())
local prim_checkable_term_type = value.prim_user_defined_type({ name = "checkable_term" }, array(value)())
-- return ok, err
local prim_lua_error_type = value.prim_user_defined_type({ name = "lua_error_type" }, array(value)())

---@class DeclConsContainer
local DeclCons = --[[@enum DeclCons]]
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
	return value.enum_value(DeclCons.cons, tup_val(...))
end

local empty = value.enum_value(DeclCons.empty, tup_val())
local unit_type = value.tuple_type(empty)
local unit_val = tup_val()

for _, deriver in ipairs { derivers.as, derivers.eq, derivers.diff } do
	checkable_term:derive(deriver)
	inferrable_term:derive(deriver)
	typed_term:derive(deriver)
	visibility:derive(deriver)
	free:derive(deriver)
	value:derive(deriver)
	neutral_value:derive(deriver)
	binding:derive(deriver)
	expression_goal:derive(deriver)
	placeholder_debug:derive(deriver)
	purity:derive(deriver)
	result_info:derive(deriver)
end
-- deriving `as` implies deriving `unwrap` in enums, but not in records
placeholder_debug:derive(derivers.unwrap)
result_info:derive(derivers.unwrap)

--[[
local tuple_defn = value.enum_value("variant",
	tup_val(
		value.enum_value("variant",
			tup_val(
				value.enum_value("empty", tup_val()),
				value.prim "element",
				value.closure()
			)
		),


	)
)]]

local terms = {
	metavariable_mt = metavariable_mt,
	checkable_term = checkable_term, -- {}
	inferrable_term = inferrable_term, -- {}
	typed_term = typed_term, -- {}
	free = free,
	visibility = visibility,
	purity = purity,
	result_info = result_info,
	value = value,
	neutral_value = neutral_value,
	binding = binding,
	expression_goal = expression_goal,
	prim_syntax_type = prim_syntax_type,
	prim_environment_type = prim_environment_type,
	prim_typed_term_type = prim_typed_term_type,
	prim_goal_type = prim_goal_type,
	prim_inferrable_term_type = prim_inferrable_term_type,
	prim_checkable_term_type = prim_checkable_term_type,
	prim_lua_error_type = prim_lua_error_type,

	runtime_context = runtime_context,
	typechecking_context = typechecking_context,
	module_mt = module_mt,
	runtime_context_type = runtime_context_type,
	typechecking_context_type = typechecking_context_type,

	DeclCons = DeclCons,
	tup_val = tup_val,
	cons = cons,
	empty = empty,
	unit_type = unit_type,
	unit_val = unit_val,
}

local override_prettys = require("./terms-pretty.lua")(terms)
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

local internals_interface = require "./internals-interface"
internals_interface.terms = terms
return terms
