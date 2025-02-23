-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>
-- provide ways to construct all terms
-- checker untyped term and typechecking context -> typed term
-- evaluator takes typed term and runtime context -> value

-- type checker monad
-- error handling and metavariable unification facilities
--
-- typechecker is allowed to fail, typechecker monad carries failures upwards
--   for now fail fast, but design should vaguely support multiple failures

local fibbuf = require "fibonacci-buffer"
local pretty_printer = require "pretty-printer"
local s = pretty_printer.s

local gen = require "terms-generators"
local derivers = require "derivers"
local traits = require "traits"
local U = require "alicorn-utils"

local format = require "format"

local map = gen.declare_map
local array = gen.declare_array
local set = gen.declare_set

---@module "types.checkable"
local checkable_term = gen.declare_type()
---@module "types.unanchored_inferrable"
local unanchored_inferrable_term = gen.declare_type()
---@module "types.anchored_inferrable"
local anchored_inferrable_term = gen.declare_type()
---@module "types.typed"
local typed_term = gen.declare_type()
---@module "types.free"
local free = gen.declare_type()
---@module "types.strict_value"
local strict_value = gen.declare_type()
---@module "types.stuck_value"
local stuck_value = gen.declare_type()
---@module "types.flex_value"
local flex_value = gen.declare_type()
---@module "types.flex_runtime_context_type"
local flex_runtime_context_type = gen.declare_type()
---@module "types.binding"
local binding = gen.declare_type()
---@module "types.expression_goal"
local expression_goal = gen.declare_type()

---@class Metavariable
--- a unique key that denotes this metavariable in the graph
---@field value integer
--- a unique key that denotes this metavariable in the graph
---@field usage integer
--- indicates if this metavariable should be solved with trait search or biunification
---@field trait boolean
--- this probably shouldn't be inside the metavariable
---@field block_level integer
local Metavariable = {}

---@return stuck_value
function Metavariable:as_stuck()
	return U.notail(stuck_value.free(free.metavariable(self)))
end

---@return flex_value
function Metavariable:as_flex()
	return U.notail(flex_value.stuck(self:as_stuck()))
end

local metavariable_mt = { __index = Metavariable }
local metavariable_type = gen.declare_foreign(gen.metatable_equality(metavariable_mt), "Metavariable")

local anchor_type = gen.declare_foreign(gen.metatable_equality(format.anchor_mt), "Anchor")
local span_type = gen.declare_foreign(gen.metatable_equality(format.span_mt), "Span")

traits.diff:implement_on(metavariable_type, {
	---@param left Metavariable
	---@param right Metavariable
	diff = function(left, right)
		print("diffing metavariables:")
		if left.value ~= right.value then
			print("left value ~= right value: " .. left.value .. " ~= " .. right.value)
		end
		if left.usage ~= right.usage then
			print("left usage ~= right usage: " .. left.usage .. " ~= " .. right.usage)
		end
		if left.block_level ~= right.block_level then
			print("left block_level ~= right block_level: " .. left.block_level .. " ~= " .. right.block_level)
		end
		if left.trait ~= right.trait then
			if left.trait then
				print("left metavariable is a trait, but right isn't!")
			else
				print("right metavariable is a trait, but left isn't!")
			end
		end
	end,
})

---@module "types.spanned_name"
local spanned_name = gen.declare_record("spanned_name", {
	"name",
	gen.builtin_string,
	"name_span",
	span_type,
})

---@class (exact) FlexRuntimeContext
---@field bindings FibonacciBuffer
---@field stuck_count integer
local FlexRuntimeContext = {}

-- without this, some flex_value.closure comparisons fail erroneously
---@class RuntimeContextBinding<T>: { name: string, val: T, debuginfo: debuginfo }
local RuntimeContextBinding = {
	__eq = function(l, r)
		return l.name == r.name and l.val == r.val
	end,
}

function FlexRuntimeContext:dump_names()
	for i = 1, self.bindings:len() do
		print(i, self.bindings:get(i).name)
	end
end

---@return string
function FlexRuntimeContext:format_names()
	local msg = ""
	for i = 1, self.bindings:len() do
		msg = msg .. tostring(i) .. "\t" .. self.bindings:get(i).name .. "\n"
	end
	return msg
end

---@param index integer
---@return flex_value?
---@return spanned_name?
function FlexRuntimeContext:get(index)
	local binding = self.bindings:get(index)
	if binding == nil then
		return nil
	end
	return binding.val, binding.debuginfo
end

---@param index integer
---@return string?
function FlexRuntimeContext:get_name(index)
	local binding = self.bindings:get(index)
	if binding == nil then
		return nil
	end
	return binding.name
end

---@param index integer
---@return spanned_name?
function FlexRuntimeContext:get_spanned_name(index)
	local binding = self.bindings:get(index)
	if binding == nil then
		return nil
	end
	return binding.debuginfo
end

---@param v flex_value
---@param name string?
---@param debuginfo spanned_name
---@return FlexRuntimeContext
function FlexRuntimeContext:append(v, name, debuginfo)
	if debuginfo == nil then
		error("null debuginfo appended to FlexRuntimeContext")
	end
	name = name or debuginfo.name -- ("#r_ctx%d"):format(self.bindings:len() + 1) -- once switchover to debug is complete, no binding should ever enter the environment without debug info and so this name fallback can be removed
	if name == nil then
		error("All variables MUST have debug information!")
	end
	local copy = {
		provenance = self,
		stuck_count = self.stuck_count,
		bindings = self.bindings:append(
			setmetatable({ name = name, val = v, debuginfo = debuginfo }, RuntimeContextBinding)
		),
	}
	if v:is_stuck() then
		copy.stuck_count = copy.stuck_count + 1
	end
	return setmetatable(copy, getmetatable(self))
end

---@param index integer
---@param v flex_value
---@return FlexRuntimeContext
function FlexRuntimeContext:set(index, v)
	local old = self.bindings:get(index)
	local new = setmetatable({ name = old.name, val = v }, RuntimeContextBinding)
	local copy = { provenance = self, stuck_count = self.stuck_count, bindings = self.bindings:set(index, new) }

	if old.val:is_stuck() then
		copy.stuck_count = copy.stuck_count - 1
	end
	if v:is_stuck() then
		copy.stuck_count = copy.stuck_count + 1
	end
	return setmetatable(copy, getmetatable(self))
end

---@param other FlexRuntimeContext
---@return boolean
function FlexRuntimeContext:eq(other)
	local omt = getmetatable(other)
	if omt ~= getmetatable(self) then
		return false
	end
	return self.bindings == other.bindings
end

---@class StrictRuntimeContext : FlexRuntimeContext
local StrictRuntimeContext = U.shallow_copy(FlexRuntimeContext)

---@param index integer
---@return strict_value
---@return spanned_name?
function StrictRuntimeContext:get(index)
	return U.notail(FlexRuntimeContext.get(self, index):unwrap_strict())
end

---@param index integer
---@return string?
function StrictRuntimeContext:get_name(index)
	local binding = self:get(index)
	if binding == nil then
		return nil
	end
	return binding.name
end

---@param index integer
---@return spanned_name?
function StrictRuntimeContext:get_spanned_name(index)
	local binding = self:get(index)
	if binding == nil then
		return nil
	end
	return binding.debuginfo
end

---@param v strict_value
---@param name string?
---@param debuginfo spanned_name
---@return StrictRuntimeContext
function StrictRuntimeContext:append(v, name, debuginfo)
	if strict_value.value_check(v) ~= true then
		error("StrictRuntimeContext:append v must be a strict_value")
	end
	---@type StrictRuntimeContext
	return U.notail(FlexRuntimeContext.append(self, flex_value.strict(v), name, debuginfo))
end

---@param index integer
---@param v strict_value
---@return StrictRuntimeContext
function StrictRuntimeContext:set(index, v)
	if strict_value.value_check(v) ~= true then
		error("StrictRuntimeContext:set v must be a strict_value")
	end
	---@type StrictRuntimeContext
	return U.notail(FlexRuntimeContext.set(self, index, flex_value.strict(v)))
end

local strict_runtime_context_mt = {
	__index = StrictRuntimeContext,
	__eq = StrictRuntimeContext.eq,
	__tostring = function(t)
		return "StrictRuntimeContext with " .. t.bindings:len() .. " bindings."
	end,
}

---@return StrictRuntimeContext
local function strict_runtime_context()
	return setmetatable({ stuck_count = 0, bindings = fibbuf() }, strict_runtime_context_mt)
end

local flex_runtime_context_mt = {
	__index = FlexRuntimeContext,
	__eq = FlexRuntimeContext.eq,
	__tostring = function(t)
		return "FlexRuntimeContext with " .. t.bindings:len() .. " bindings."
	end,
}

---@return FlexRuntimeContext
local function flex_runtime_context()
	return setmetatable({ stuck_count = 0, bindings = fibbuf() }, flex_runtime_context_mt)
end

---@return StrictRuntimeContext
function FlexRuntimeContext:as_strict()
	if self.stuck_count > 0 then
		error("Cannot convert runtime context to strict, found " .. tostring(self.stuck_count) .. " stuck bindings!")
	end
	return setmetatable(
		{ provenance = self, stuck_count = self.stuck_count, bindings = self.bindings },
		strict_runtime_context_mt
	)
end

---@return FlexRuntimeContext
function StrictRuntimeContext:as_flex()
	return setmetatable(
		{ provenance = self, stuck_count = self.stuck_count, bindings = self.bindings },
		flex_runtime_context_mt
	)
end

local function runtime_context_diff_fn(left, right)
	print("diffing runtime context...")
	local rt = getmetatable(right)
	if getmetatable(left) ~= rt then
		print("unequal types!")
		print(getmetatable(left))
		print(rt)
		print("stopping diff")
		return
	end
	if left.bindings:len() ~= right.bindings:len() then
		print("unequal lengths!")
		print(left.bindings:len())
		print(right.bindings:len())
		print("stopping diff")
		return
	end
	local n = 0
	local diff_elems = {}
	for i = 1, left.bindings:len() do
		if left:get(i) ~= right:get(i) then
			n = n + 1
			diff_elems[n] = i
		end
	end
	if n == 0 then
		print("no difference")
		print("stopping diff")
		return
	elseif n == 1 then
		local d = diff_elems[1]
		print("difference in element: " .. tostring(d))
		local diff_impl
		if rt == flex_runtime_context_mt then
			diff_impl = traits.diff:get(flex_value)
		elseif rt == strict_runtime_context_mt then
			diff_impl = traits.diff:get(strict_value)
		end
		-- tail call
		return diff_impl.diff(left:get(d), right:get(d))
	else
		print("difference in multiple elements:")
		for i = 1, n do
			print("left " .. tostring(diff_elems[i]) .. ": " .. tostring(left:get(diff_elems[i])))
			print("right " .. tostring(diff_elems[i]) .. ": " .. tostring(right:get(diff_elems[i])))
		end
		print("stopping diff")
		return
	end
end

local typechecking_context_mt

---@class TypecheckingContext
---@field runtime_context FlexRuntimeContext
---@field bindings FibonacciBuffer
local TypecheckingContext = {}

---@param ctx FlexRuntimeContext|TypecheckingContext
---@return FlexRuntimeContext
local function to_runtime_context(ctx)
	if getmetatable(ctx) == typechecking_context_mt then
		return ctx.runtime_context
	end
	return ctx
end

---@param v table
---@param ctx FlexRuntimeContext|TypecheckingContext
---@param values flex_value[]
---@return boolean
local function verify_placeholders(v, ctx, values)
	-- If it's not a table we don't care
	if type(v) ~= "table" then
		return true
	end

	ctx = to_runtime_context(ctx)

	-- Special handling for arrays
	if getmetatable(v) and getmetatable(getmetatable(v)) == gen.array_type_mt then
		for k, val in ipairs(v) do
			if not verify_placeholders(val, ctx, values) then
				return false
			end
		end
		return true
	end
	if not v.kind then
		return true
	end

	if v.kind == "free.placeholder" then
		local i, info = v:unwrap_placeholder()
		if info then
			local source_ctx = ctx

			while source_ctx do
				if source_ctx == info.ctx then
					return true
				end

				source_ctx = source_ctx.provenance
			end

			print(
				debug.traceback(
					"INVALID PROVENANCE: "
						.. tostring(info)
						.. "\nORIGINAL CTX: "
						.. info.ctx:format_names()
						.. "\nASSOCIATED CTX: "
						.. ctx:format_names()
				)
			)
			--error("")
			os.exit(-1, true)

			return false
		end
	elseif v.kind == "free.metavariable" then
		if not values then
			error(debug.traceback("FORGOT values PARAMETER!"))
		end
		---@type Metavariable
		local mv = v:unwrap_metavariable()

		local source_ctx = ctx

		local mv_ctx = to_runtime_context(values[mv.value][3])
		while source_ctx do
			if source_ctx == mv_ctx then
				return true
			end

			source_ctx = source_ctx.provenance
		end

		-- for now we just check to see if the first two parts are valid
		if ctx:get(1) == mv_ctx:get(1) then
			return true
		end
		print("dumping metavariable paths")
		source_ctx = ctx
		while source_ctx do
			print(source_ctx)
			source_ctx = source_ctx.provenance
		end

		print("----")
		source_ctx = mv_ctx
		while source_ctx do
			print(source_ctx)
			source_ctx = source_ctx.provenance
		end
		print(
			debug.traceback(
				"INVALID METAVARIABLE PROVENANCE: "
					.. tostring(v)
					.. "\nORIGINAL CTX: "
					.. tostring(values[mv.value][3])
					.. "\n"
					.. values[mv.value][3]:format_names()
					.. "\nASSOCIATED CTX: "
					.. tostring(ctx)
					.. "\n"
					.. ctx:format_names()
			)
		)
		--error("")
		os.exit(-1, true)
		return false
	end

	for k, val in pairs(v) do
		if k ~= "cause" then
			if not verify_placeholders(val, ctx, values) then
				return false
			end
		end
	end

	return true
end

---get the name of a binding in a TypecheckingContext
---@param index integer
---@return string
function TypecheckingContext:get_name(index)
	local binding = self.bindings:get(index)
	if binding == nil then
		return nil
	end
	return binding.name
end

---get the name of a binding in a TypecheckingContext
---@param index integer
---@return spanned_name?
function TypecheckingContext:get_spanned_name(index)
	local binding = self.bindings:get(index)
	if binding == nil then
		return nil
	end
	return binding.debuginfo
end

function TypecheckingContext:dump_names()
	for i = 1, self:len() do
		print(i, tostring(self:get_name(i)))
	end
end

---@return string
function TypecheckingContext:format_names()
	local msg = {}
	for i = 1, self:len() do
		msg[(i * 3) - 2] = tostring(i)
		msg[(i * 3) - 1] = "\t"
		msg[i * 3] = tostring(self:get_name(i))
	end
	return table.concat(msg, "\n")
end

---@return string
function TypecheckingContext:format_names_and_types()
	local msg = ""
	for i = 1, self:len() do
		msg[(i * 5) - 4] = tostring(i)
		msg[(i * 5) - 3] = "\t"
		msg[(i * 5) - 2] = tostring(self:get_name(i))
		msg[(i * 5) - 1] = "\t:\t"
		msg[i * 5] = self:get_type(i):pretty_print(self)
	end
	return table.concat(msg, "\n")
end

---@param index integer
---@return flex_value
function TypecheckingContext:get_type(index)
	return self.bindings:get(index).type
end

function TypecheckingContext:DEBUG_VERIFY_VALUES(state)
	for i = 1, self:len() do
		verify_placeholders(self:get_type(i), self, state.values)
	end
end

---@return FlexRuntimeContext
function TypecheckingContext:get_runtime_context()
	return self.runtime_context
end

---@param name string
---@param type flex_value
---@param val flex_value?
---@param debuginfo spanned_name
---@return TypecheckingContext
function TypecheckingContext:append(name, type, val, debuginfo)
	if gen.builtin_string.value_check(name) ~= true then
		error("TypecheckingContext:append parameter 'name' must be a string")
	end
	if flex_value.value_check(type) ~= true then
		print("type", type)
		p(type)
		for k, v in pairs(type) do
			print(k, v)
		end
		print(getmetatable(type))
		error("TypecheckingContext:append parameter 'type' must be a flex_value")
	end
	if type:is_closure() then
		error "BUG!!!"
	end
	if val ~= nil and flex_value.value_check(val) ~= true then
		error("TypecheckingContext:append parameter 'val' must be a flex_value (or nil if given start_anchor)")
	end
	if debuginfo ~= nil and spanned_name.value_check(debuginfo) ~= true then
		error("TypecheckingContext:append parameter 'debuginfo' must be a spanned_name (or nil if given val)")
	end
	if not val and not debuginfo then
		error("TypecheckingContext:append expected either val or debuginfo")
	end
	if not val then
		--debuginfo["{TRACE}"] = U.bound_here(2)
		val = flex_value.stuck(stuck_value.free(free.placeholder(self:len() + 1, debuginfo)))
	end

	local copy = {
		bindings = self.bindings:append({ name = name, type = type }),
		runtime_context = self.runtime_context:append(val, name, debuginfo),
	}
	return setmetatable(copy, typechecking_context_mt)
end

---@return integer
function TypecheckingContext:len()
	return U.notail(self.bindings:len())
end

typechecking_context_mt = {
	__index = TypecheckingContext,
	__len = TypecheckingContext.len,
	__tostring = function(t)
		return "TypecheckingContext with " .. t.bindings:len() .. " bindings. " .. tostring(t.runtime_context)
	end,
}

---@return TypecheckingContext
local function typechecking_context()
	return setmetatable({ bindings = fibbuf(), runtime_context = flex_runtime_context() }, typechecking_context_mt)
end

-- empty for now, just used to mark the table
local module_mt = {}

local strict_runtime_context_type =
	gen.declare_foreign(gen.metatable_equality(strict_runtime_context_mt), "StrictRuntimeContext")
local flex_runtime_context_type =
	gen.declare_foreign(gen.metatable_equality(flex_runtime_context_mt), "FlexRuntimeContext")
local typechecking_context_type =
	gen.declare_foreign(gen.metatable_equality(typechecking_context_mt), "TypecheckingContext")
local host_user_defined_id = gen.declare_foreign(function(val)
	return type(val) == "table" and type(val.name) == "string"
end, "{ name: string }")

traits.diff:implement_on(strict_runtime_context_type, { diff = runtime_context_diff_fn })
traits.diff:implement_on(flex_runtime_context_type, { diff = runtime_context_diff_fn })

-- implicit arguments are filled in through unification
-- e.g. fn append(t : star(0), n : nat, xs : Array(t, n), val : t) -> Array(t, n+1)
--      t and n can be implicit, given the explicit argument xs, as they're filled in by unification
---@module "types.visibility"
local visibility = gen.declare_enum("visibility", {
	{ "explicit" },
	{ "implicit" },
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
	{ "dependent", { "val", flex_value } },
	{ "inherit" },
})

expression_goal:define_enum("expression_goal", {
	-- infer
	{ "infer" },
	-- check to a goal type
	{ "check", { "goal_type", flex_value } },
	-- TODO
	{ "mechanism", { "TODO", flex_value } },
})

-- terms that don't have a body yet
-- stylua: ignore
binding:define_enum("binding", {
	{ "let", {
		"name", gen.builtin_string,
		"debug", spanned_name,
		"expr", anchored_inferrable_term,
	} },
	{ "tuple_elim", {
		"names",   array(gen.builtin_string),
		"debug", array(spanned_name),
		"subject", anchored_inferrable_term,
	} },
	{ "annotated_lambda", {
		"param_name",       gen.builtin_string,
		"param_annotation", anchored_inferrable_term,
		"start_anchor",     anchor_type,
		"visible",          visibility,
		"pure",             checkable_term,
	} },
	{ "program_sequence", {
		"first",        anchored_inferrable_term,
		"start_anchor", anchor_type,
	} },
})

-- checkable terms need a goal type to typecheck against
-- stylua: ignore
checkable_term:define_enum("checkable", {
	{ "inferrable", { "inferrable_term", anchored_inferrable_term } },
	{ "tuple_cons", {
		"elements", array(checkable_term),
		"debug", array(spanned_name),
	} },
	{ "host_tuple_cons", {
		"elements", array(checkable_term),
		"debug", array(spanned_name),
	} },
	{ "lambda", {
		"param_name", gen.builtin_string,
		"body",       checkable_term,
	} },
})

-- inferrable terms can have their type inferred / don't need a goal type
-- stylua: ignore
unanchored_inferrable_term:define_enum("unanchored_inferrable", {
	{ "bound_variable", { "index", gen.builtin_integer, "debug", spanned_name } },
	{ "typed", {
		"type",         typed_term,
		"usage_counts", array(gen.builtin_integer),
		"typed_term",   typed_term,
	} },
	{ "annotated_lambda", {
		"param_name",       gen.builtin_string,
		"param_annotation", anchored_inferrable_term,
		"body",             anchored_inferrable_term,
		"start_anchor",     anchor_type,
		"visible",          visibility,
		"pure",             checkable_term,
	} },
	{ "pi", {
		"param_type",  anchored_inferrable_term,
		"param_info",  checkable_term,
		"result_type", anchored_inferrable_term,
		"result_info", checkable_term,
	} },
	{ "application", {
		"f",   anchored_inferrable_term,
		"arg", checkable_term,
	} },
	{ "tuple_cons", {
		"elements", array(anchored_inferrable_term),
		"debug", array(spanned_name),
	} },
	{ "tuple_elim", {
		"names",   array(gen.builtin_string),
		"debug", array(spanned_name),
		"subject", anchored_inferrable_term,
		"body",    anchored_inferrable_term,
	} },
	{ "tuple_type", { "desc", anchored_inferrable_term } },
	{ "record_cons", { "fields", map(gen.builtin_string, anchored_inferrable_term) } },
	{ "record_elim", {
		"subject",     anchored_inferrable_term,
		"field_names", array(gen.builtin_string),
		"debug_ids",   array(spanned_name),
		"body",        anchored_inferrable_term,
	} },
	{ "enum_cons", {
		"constructor", gen.builtin_string,
		"arg",         anchored_inferrable_term,
	} },
	{ "enum_desc_cons", {
		"variants", map(gen.builtin_string, anchored_inferrable_term),
		"rest",     anchored_inferrable_term,
	} },
	{ "enum_elim", {
		"subject",   anchored_inferrable_term,
		"mechanism", anchored_inferrable_term,
	} },
	{ "enum_type", { "desc", anchored_inferrable_term } },
	{ "enum_case", {
		"target",   anchored_inferrable_term,
		"variants", map(gen.builtin_string, anchored_inferrable_term),
		"variant_debug", map(gen.builtin_string, spanned_name), -- would be better to make this a single map with a pair value
		--"default",  inferrable_term,
	} },
	{ "enum_absurd", {
		"target", anchored_inferrable_term,
		"debug",  gen.builtin_string,
	} },

	{ "object_cons", { "methods", map(gen.builtin_string, anchored_inferrable_term) } },
	{ "object_elim", {
		"subject",   anchored_inferrable_term,
		"mechanism", anchored_inferrable_term,
	} },
	{ "let", {
		"name", gen.builtin_string,
		"debug", spanned_name,
		"expr", anchored_inferrable_term,
		"body", anchored_inferrable_term,
	} },
	{ "operative_cons", {
		"operative_type", anchored_inferrable_term,
		"userdata",       anchored_inferrable_term,
	} },
	{ "operative_type_cons", {
		"userdata_type", anchored_inferrable_term,
		"handler",       checkable_term,
	} },
	{ "level_type" },
	{ "level0" },
	{ "level_suc", { "previous_level", anchored_inferrable_term } },
	{ "level_max", {
		"level_a", anchored_inferrable_term,
		"level_b", anchored_inferrable_term,
	} },
	--{"star"},
	--{"prop"},
	--{"prim"},
	{ "annotated", {
		"annotated_term", checkable_term,
		"annotated_type", anchored_inferrable_term,
	} },
	{ "host_tuple_cons", {
		"elements", array(anchored_inferrable_term),
		"debug", array(spanned_name),
	} }, -- host_value
	{ "host_user_defined_type_cons", {
		"id",          host_user_defined_id, -- host_user_defined_type
		"family_args", array(anchored_inferrable_term), -- host_value
	} },
	{ "host_tuple_type", { "desc", anchored_inferrable_term } }, -- just like an ordinary tuple type but can only hold host_values
	{ "host_function_type", {
		"param_type",  anchored_inferrable_term, -- must be a host_tuple_type
		-- host functions can only have explicit arguments
		"result_type", anchored_inferrable_term, -- must be a host_tuple_type
		"result_info", checkable_term,
	} },
	{ "host_wrapped_type", { "type", anchored_inferrable_term } },
	{ "host_unstrict_wrapped_type", { "type", anchored_inferrable_term } },
	{ "host_wrap", { "content", anchored_inferrable_term } },
	{ "host_unstrict_wrap", { "content", anchored_inferrable_term } },
	{ "host_unwrap", { "container", anchored_inferrable_term } },
	{ "host_unstrict_unwrap", { "container", anchored_inferrable_term } },
	{ "host_if", {
		"subject",    checkable_term, -- checkable because we always know must be of host_bool_type
		"consequent", anchored_inferrable_term,
		"alternate",  anchored_inferrable_term,
	} },
	{ "host_intrinsic", {
		"source",       checkable_term,
		"type",         anchored_inferrable_term, --checkable_term,
		"start_anchor", anchor_type,
	} },
	{ "program_sequence", {
		"first",        anchored_inferrable_term,
		"start_anchor", anchor_type,
		"continue",     anchored_inferrable_term,
		"debug_info",	spanned_name,
	} },
	{ "program_end", { "result", anchored_inferrable_term } },
	{ "program_type", {
		"effect_type", anchored_inferrable_term,
		"result_type", anchored_inferrable_term,
	} },
})

-- function Alice wants to assign the value True (of type SingletonTrue) to variable Foo,
-- which means that SingletonTrue must be a subtype of FooT (the type metavariable for Foo's type).
-- function Bob wants to consume the value Foo as always the value False (of type SingletonFalse),
-- which means that Bob wants FooT to be a subtype of SingletonFalse.
--
-- on behalf of Bob, Alicorn will, _very_ early,
-- call `TypeCheckerState:flow(`[`flex_value` for FooT]`, `[`TypecheckingContext` for FooT]`, `[`flex_value` for SingletonFalse]`, `[`TypecheckingContext` for SingletonFalse]`, cause)`.
-- that'll call out to `TypeCheckerState:constrain(`[`flex_value` for FooT]`, `[`TypecheckingContext` for FooT]`, `[`flex_value` for SingletonFalse]`, `[`TypecheckingContext` for SingletonFalse]`, UniverseOmegaRelation, cause)`.
-- that'll queue an `EdgeNotif.constrain(`[`flex_value` for FooT]`, UniverseOmegaRelation, `[`flex_value` for SingletonFalse]`, self` (as `TypeCheckerState`)`.block_level, cause)`, to be processed within that last `TypeCheckerState:constrain` call.

-- stylua: ignore
anchored_inferrable_term:define_record("anchored_inferrable", {
	"anchor",
	anchor_type,
	"term",
	unanchored_inferrable_term,
})

---@class SubtypeRelation
---@field debug_name string
--- : (val:T, use:T) -> Prop__\
--- Construct a subtyping relation (val :> use), that type val is a supertype of type use, i.e. that type use is a subtype of type val, i.e. that type val flows into type use.
--- Lua value is currently used only for reference equality?
---@field Rel strict_value
--- : (a:T) -> Rel(a,a)\
--- Construct a reflexive subtyping relation—that a type flows into itself.
--- Lua value is currently unused?
---@field refl strict_value
--- : (a:T, b:T, Rel(a,b), Rel(b,a)) -> a == b\
--- Lua value is currently unused?
---@field antisym strict_value
--- : (val:Node(T), use:Node(T)) -> [TCState] (Error)\
--- Work with the ambient typechecker state to constrain that type val flows into type use.
---@field constrain strict_value
local subtype_relation_mt = {}

local SubtypeRelation = gen.declare_foreign(gen.metatable_equality(subtype_relation_mt), "SubtypeRelation")

subtype_relation_mt.__tostring = function(self)
	return "«" .. self.debug_name .. "»"
end

---@module 'types.constraintcause'
local constraintcause = gen.declare_type()

-- stylua: ignore
constraintcause:define_enum("constraintcause", {
	{ "primitive", {
		"description", gen.builtin_string,
		"position",    anchor_type,
		"track", gen.any_lua_type,
	} },
	{ "composition", {
		"left",     gen.builtin_integer,
		"right",    gen.builtin_integer,
		"position", anchor_type,
	} },
	{ "nested", {
		"description", gen.builtin_string,
		"inner",     constraintcause,
	} },
	{ "leftcall_discharge", {
		"call",       gen.builtin_integer,
		"constraint", gen.builtin_integer,
		"position",   anchor_type,
	} },
	{ "rightcall_discharge", {
		"constraint", gen.builtin_integer,
		"call",       gen.builtin_integer,
		"position",   anchor_type,
	} },
	{ "lost", { --Information has been lost, please generate any information you can to help someone debug the lost information in the future
		"unique_string", gen.builtin_string,
		"stacktrace",    gen.builtin_string,
		"auxiliary",     gen.any_lua_type,
	} },
})

---@module 'types.constraintelem'
-- stylua: ignore
local constraintelem = gen.declare_enum("constraintelem", {
	{ "sliced_constrain", {
		"rel",      SubtypeRelation,
		"right",    typed_term,
		"rightctx", typechecking_context_type,
		"cause",    constraintcause,
	} },
	{ "constrain_sliced", {
		"left",    typed_term,
		"leftctx", typechecking_context_type,
		"rel",     SubtypeRelation,
		"cause",   constraintcause,
	} },
	{ "sliced_leftcall", {
		"arg",      typed_term,
		"rel",      SubtypeRelation,
		"right",    typed_term,
		"rightctx", typechecking_context_type,
		"cause",    constraintcause,
	} },
	{ "leftcall_sliced", {
		"left",    typed_term,
		"leftctx", typechecking_context_type,
		"arg",     typed_term,
		"rel",     SubtypeRelation,
		"cause",   constraintcause,
	} },
	{ "sliced_rightcall", {
		"rel",      SubtypeRelation,
		"right",    typed_term,
		"rightctx", typechecking_context_type,
		"arg",      typed_term,
		"cause",    constraintcause,
	} },
	{ "rightcall_sliced", {
		"left",    typed_term,
		"leftctx", typechecking_context_type,
		"rel",     SubtypeRelation,
		"arg",     typed_term,
		"cause",   constraintcause,
	} },
})

local unique_id = gen.builtin_table

-- typed terms have been typechecked but do not store their type internally
-- stylua: ignore
typed_term:define_enum("typed", {
	{ "bound_variable", { "index", gen.builtin_integer, "debug", spanned_name } },
	{ "literal", { "literal_value", strict_value } },
	{ "metavariable", { "metavariable", metavariable_type } },
	{ "unique", { "id", unique_id } },
	{ "lambda", {
		"param_name", gen.builtin_string,
		"param_debug", spanned_name,
		"body",       typed_term,
		"capture",    typed_term,
		"capture_dbg", spanned_name,
		"start_anchor",     anchor_type,
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
		"debug", spanned_name,
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
	{ "star", { "level", gen.builtin_integer, "depth", gen.builtin_integer } },
	{ "prop", { "level", gen.builtin_integer } },
	{ "tuple_cons", { "elements", array(typed_term) } },
	--{"tuple_extend", {"base", typed_term, "fields", array(typed_term)}}, -- maybe?
	{ "tuple_elim", {
		"names",   array(gen.builtin_string),
		"debug", array(spanned_name), -- can probably replace the names array entirely
		"subject", typed_term,
		"length",  gen.builtin_integer,
		"body",    typed_term,
	} },
	{ "tuple_element_access", {
		"subject", typed_term,
		"index",   gen.builtin_integer,
	} },
	{ "tuple_type", { "desc", typed_term } },
	{ "tuple_desc_type", { "universe", typed_term } },
	{ "tuple_desc_concat_indep", { "prefix", typed_term, "suffix", typed_term }},
	{ "record_cons", { "fields", map(gen.builtin_string, typed_term) } },
	{ "record_type_cons", {"desc", typed_term }},
	{ "record_desc_extend", {"name", typed_term, "type", typed_term}},
	{ "record_extend", {
		"base",   typed_term,
		"fields", map(gen.builtin_string, typed_term),
	} },
	{ "record_elim", {
		"subject",     typed_term,
		"field_names", array(gen.builtin_string),
		"debug_ids", array(spanned_name),
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
		"rest",     typed_term,
	} },
	{ "enum_desc_type", {
		"univ", typed_term
	} },
	{ "enum_type", { "desc", typed_term } },
	{ "enum_case", {
		"target",   typed_term,
		"variants", map(gen.builtin_string, typed_term),
		"variant_debug", map(gen.builtin_string, spanned_name), -- would be better to make this a single map with a pair value
		"default",  typed_term,
		"default_debug", spanned_name,
	} },
	{ "enum_absurd", {
		"target", typed_term,
		"debug",  gen.builtin_string,
	} },
	{ "object_cons", { "methods", map(gen.builtin_string, typed_term) } },
	{ "object_corec_cons", { "methods", map(gen.builtin_string, typed_term) } },
	{ "object_elim", {
		"subject",   typed_term,
		"mechanism", typed_term,
	} },
	{ "operative_cons", { "userdata", typed_term } },
	{ "operative_type_cons", {
		"userdata_type", typed_term,
		"handler",       typed_term,
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
	{ "host_int_fold", {"n", typed_term, "f", typed_term, "acc", typed_term}},
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
		"source",       typed_term,
		"start_anchor", anchor_type,
	} },

	-- a list of upper and lower bounds, and a relation being bound with respect to
	{ "range", {
		"lower_bounds", array(typed_term),
		"upper_bounds", array(typed_term),
		"relation",     typed_term, -- a subtyping relation. not currently represented.
	} },

	{ "singleton", {
		"supertype", typed_term,
		"value",     typed_term,
	} },

	{ "program_sequence", {
		"first",    typed_term,
		"continue", typed_term,
		"debug_info", spanned_name,
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
	{ "effect_row", {
		"elems",      array(typed_term),
		"rest",       typed_term,
	} },
	{ "effect_row_resolve", {
		"elems",      set(unique_id),
		"rest",       typed_term,
	} },
	{ "program_type", {
		"effect_type", typed_term,
		"result_type", typed_term,
	} },
	{ "srel_type", { "target_type", typed_term } },
	{ "variance_type", { "target_type", typed_term } },
	{ "variance_cons", {
		"positive", typed_term,
		"srel",     typed_term,
	} },
	{ "intersection_type", {
		"left",  typed_term,
		"right", typed_term,
	} },
	{ "union_type", {
		"left",  typed_term,
		"right", typed_term,
	} },
	{ "constrained_type", {
		"constraints", array(constraintelem),
		"ctx", typechecking_context_type,
	} },
})

---@param v table
---@param ctx TypecheckingContext
---@param nested boolean
---@return boolean
local function verify_placeholder_lite(v, ctx, nested)
	-- If it's not a table we don't care
	if type(v) ~= "table" then
		return true
	end

	-- Special handling for arrays
	local v_mt = getmetatable(v)
	if v_mt and getmetatable(v_mt) == gen.array_type_mt then
		for k, val in ipairs(v) do
			local ok, i, info, info_mismatch = verify_placeholder_lite(val, ctx, true)
			if not ok then
				if not nested then
					print(v)
					if info_mismatch ~= nil then
						print("EXPECTED INFO: " .. info_mismatch)
					end
					error("AAAAAAAAAAAAAA found " .. tostring(i))
				end
				return false, i, info
			end
		end
		return true
	end
	if not v.kind then
		return true
	end

	if v.kind == "free.placeholder" then
		local i, info = v:unwrap_placeholder()
		if i > ctx:len() or i > ctx.runtime_context.bindings:len() then
			--os.exit(-1, true)
			--error("AAAAAAAAAAAAAA found " .. tostring(i) .. " " .. tostring(info))
			return false, i, info
		end
		local info_target = ctx.runtime_context.bindings:get(i).debuginfo
		if info ~= info_target then
			return false, i, info, info_target
		end
	end

	for k, val in pairs(v) do
		if k ~= "cause" and k ~= "bindings" and k ~= "provenance" then
			local ok, i, info, info_mismatch = verify_placeholder_lite(val, ctx, true)
			if not ok then
				if not nested then
					print(v)
					if info_mismatch ~= nil then
						print("EXPECTED INFO: " .. info_mismatch)
					end
					error("AAAAAAAAAAAAAA found " .. tostring(i) .. " " .. tostring(info))
				end
				return false, i, info
			end
		end
	end

	return true
end

local orig_literal_constructor = typed_term.literal
local function literal_constructor_check(val)
	-- FIXME: make sure no placeholders in val
	verify_placeholder_lite(val, typechecking_context())
	return U.notail(orig_literal_constructor(val))
end
typed_term.literal = literal_constructor_check

-- stylua: ignore
free:define_enum("free", {
	{ "metavariable", { "metavariable", metavariable_type } },
	{ "placeholder", {
		"index", gen.builtin_integer,
		"debug", spanned_name,
	} },
	{ "unique", { "id", unique_id } },
	-- TODO: axiom
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
---@module 'types.flex_continuation'
local flex_continuation = gen.declare_type()
---@module 'types.strict_continuation'
local strict_continuation = gen.declare_type()
---@module 'types.stuck_continuation'
local stuck_continuation = gen.declare_type()

---@param tag ("strict"|"stuck")
---@param t Type
---@return Type t
local function replace_flex_type(tag, t)
	if type(t) == "string" then
		error(debug.traceback("wrong type passed to replace_flex_type"))
	end
	if t == flex_value then
		if tag == "strict" then
			return strict_value
		elseif tag == "stuck" then
			return flex_value
		end
		error("Unknown tag: " .. tag)
	elseif getmetatable(t) == gen.array_type_mt then
		---@cast t ArrayType
		return U.notail(array(replace_flex_type(tag, t.value_type)))
	elseif getmetatable(t) == gen.map_type_mt then
		---@cast t MapType
		return U.notail(map(replace_flex_type(tag, t.key_type), replace_flex_type(tag, t.value_type)))
	elseif t == flex_runtime_context_type then
		if tag == "strict" then
			return strict_runtime_context_type
		elseif tag == "stuck" then
			return flex_runtime_context_type
		end
		error("Unknown tag: " .. tag)
	elseif t == flex_continuation then
		if tag == "strict" then
			return strict_continuation
		elseif tag == "stuck" then
			return flex_continuation
		end
		error("Unknown tag: " .. tag)
	end

	return t
end
replace_flex_type = U.memoize(replace_flex_type, false)

---@param arg (Value | StrictRuntimeContext | FlexRuntimeContext)
---@param t Type
---@return ("strict"|"stuck") tag
---@return (Value | StrictRuntimeContext | FlexRuntimeContext) arg
local function specify_flex_value(arg, t)
	if t == flex_value then
		---@cast arg flex_value
		if arg:is_stuck() then
			return "stuck", arg
		end
		return "strict", U.notail(arg:unwrap_strict())
	elseif getmetatable(t) == gen.array_type_mt then
		---@cast arg ArrayValue
		---@cast t ArrayType
		local arg_value_t = t.value_type
		local arg_values, arg_strict_values, arg_values_length = arg.array, {}, arg.n
		for i = 1, arg_values_length do
			local arg_value_tag
			arg_value_tag, arg_strict_values[i] = specify_flex_value(arg_values[i], arg_value_t)
			if arg_value_tag == "stuck" then
				return "stuck", arg
			end
		end
		local arg_strict_value_t = replace_flex_type("strict", arg_value_t)
		return "strict", array(arg_strict_value_t):unchecked_new(arg_strict_values, arg_values_length)
	elseif getmetatable(t) == gen.map_type_mt then
		---@cast arg MapValue
		---@cast t MapType
		local arg_key_t, arg_value_t = t.key_type, t.value_type
		local arg_values, arg_strict_values = arg._map, {}
		for arg_key, arg_value in pairs(arg_values) do
			local arg_key_tag, arg_strict_key = specify_flex_value(arg_key, arg_key_t)
			if arg_key_tag == "stuck" then
				return "stuck", arg
			end
			local arg_value_tag
			arg_value_tag, arg_strict_values[arg_strict_key] = specify_flex_value(arg_value, arg_value_t)
			if arg_value_tag == "stuck" then
				return "stuck", arg
			end
		end
		local arg_strict_key_t = replace_flex_type("strict", arg_key_t)
		local arg_strict_value_t = replace_flex_type("strict", arg_value_t)
		return "strict", map(arg_strict_key_t, arg_strict_value_t):unchecked_new(arg_strict_values)
	elseif t == flex_continuation then
		---@cast arg flex_continuation
		if arg:is_stuck() then
			return "stuck", arg
		end
		return "strict", U.notail(arg:unwrap_strict())
	elseif t == flex_runtime_context_type then
		---@cast arg FlexRuntimeContext
		if arg.stuck_count > 0 then
			return "stuck", arg
		end
		return "strict", U.notail(arg:as_strict())
	end
	return "strict", arg
end

---@param args (Value | StrictRuntimeContext | FlexRuntimeContext)[]
---@param types Type[]
---@return ("strict" | "stuck") tag
---@return (Value | StrictRuntimeContext | FlexRuntimeContext)[] arg
local function specify_flex_values(args, types)
	local strict_args = {}
	for i, t in ipairs(types) do
		local tag, arg = specify_flex_value(args[i], t)
		if tag == "stuck" then
			return tag, args
		end
		table.insert(strict_args, arg)
	end
	return "strict", strict_args
end

---@generic T
---@param key T
---@return T key
local function unify_already_flex(val)
	return val
end

---@param t Type
---@return Type t
---@return (fun(val: (Value | StrictRuntimeContext | FlexRuntimeContext)): (flex_val: (Value | FlexRuntimeContext)))? unify
local function unify_flex_type(t)
	if t == strict_value then
		return flex_value, flex_value.strict
	elseif t == stuck_value then
		return flex_value, flex_value.stuck
	elseif t == strict_continuation then
		return flex_continuation, flex_continuation.strict
	elseif t == stuck_continuation then
		return flex_continuation, flex_continuation.stuck
	elseif t == strict_runtime_context_type then
		return flex_runtime_context_type, StrictRuntimeContext.as_flex
	end
	local t_mt = getmetatable(t)
	if t_mt == gen.array_type_mt then
		---@cast t ArrayType
		local value_t = t.value_type
		local flex_value_t, unify_value = unify_flex_type(value_t)
		if unify_value == nil then
			return t, nil
		end
		---@cast unify_value -nil
		local flex_t = array(flex_value_t)
		---@param values ArrayValue
		---@return ArrayValue flex_value
		local function unify(values)
			return U.notail(values:map(flex_t, unify_value))
		end
		return flex_t, unify
	elseif t_mt == gen.map_type_mt then
		---@cast t MapType
		local key_t, value_t = t.key_type, t.value_type
		local flex_key_t, unify_key = unify_flex_type(key_t)
		local flex_value_t, unify_value = unify_flex_type(value_t)
		if unify_key == nil and unify_value == nil then
			return t, nil
		end
		if unify_key == nil then
			unify_key = unify_already_flex
		end
		if unify_value == nil then
			unify_value = unify_already_flex
		end
		local flex_t = map(flex_key_t, flex_value_t)
		---@param vals MapValue
		---@return MapValue flex_vals
		local function unify(vals)
			---@type (Value | FlexRuntimeContext)[]
			local flex_vals = {}
			for key, val in pairs(vals._map) do
				local flex_key, flex_val = unify_key(key), unify_value(val)
				flex_vals[flex_key] = flex_val
			end
			return U.notail(flex_t:unchecked_new(flex_vals))
		end
		return flex_t, unify
	end
	return t, nil
end
unify_flex_type = U.memoize(unify_flex_type, false)

---@param arg (Value | StrictRuntimeContext | FlexRuntimeContext)
---@return (Value | FlexRuntimeContext) arg
local function unify_flex_value(arg)
	local arg_mt = getmetatable(arg)
	local _strict_t, unify = unify_flex_type(arg_mt)
	if unify ~= nil then
		return U.notail(unify(arg))
	end
	return arg
end

---@param args (Value | StrictRuntimeContext | FlexRuntimeContext)[]
---@return (Value | FlexRuntimeContext)[] arg
local function unify_flex_values(args)
	---@type (Value | FlexRuntimeContext)[]
	local flex_args = {}
	for i, v in ipairs(args) do
		flex_args[i] = unify_flex_value(v)
	end
	return flex_args
end

-- stylua: ignore
gen.define_multi_enum(flex_continuation, "flex_continuation", replace_flex_type, specify_flex_values, unify_flex_values,
{ strict = strict_continuation, stuck = stuck_continuation },
{ strict = "strict_continuation", stuck = "stuck_continuation" },
{
	{ "empty$strict" },
	{ "frame$flex", {
		"context", flex_runtime_context_type,
		"code",    typed_term,
	} },
	{ "sequence$flex", {
		"first",  flex_continuation,
		"second", flex_continuation,
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
gen.define_multi_enum(
	flex_value,
	"flex_value",
	replace_flex_type,
	specify_flex_values,
	unify_flex_values,
	{ strict = strict_value, stuck = stuck_value },
	{ strict = "strict_value", stuck = "stuck_value" },
	{
		-- explicit, implicit,
		{ "visibility_type$strict" },
		{ "visibility$strict", { "visibility", visibility } },
		-- info about the parameter (is it implicit / what are the usage restrictions?)
		-- quantity/visibility should be restricted to free or (quantity/visibility) rather than any value
		{ "param_info_type$strict" },
		{ "param_info$flex", { "visibility", flex_value } },
		-- whether or not a function is effectful /
		-- for a function returning a monad do i have to be called in an effectful context or am i pure
		{ "result_info_type$strict" },
		{ "result_info$strict", { "result_info", result_info } },
		{ "pi$flex", {
			"param_type",  flex_value,
			"param_info",  flex_value, -- param_info
			"result_type", flex_value, -- closure from input -> result
			"result_info", flex_value, -- result_info
		}, },
		-- closure is a type that contains a typed term corresponding to the body
		-- and a runtime context representing the bound context where the closure was created
		{ "closure$flex", {
			"param_name", gen.builtin_string,
			"code",       typed_term,
			"capture",    flex_value,
			"capture_dbg", spanned_name,
			"param_debug",      spanned_name,
		}, },
		-- a list of upper and lower bounds, and a relation being bound with respect to
		{ "range$flex", {
			"lower_bounds", array(flex_value),
			"upper_bounds", array(flex_value),
			"relation",     strict_value, -- a subtyping relation. not currently represented.
		}, },
		{ "name_type$strict" },
		{ "name$strict", { "name", gen.builtin_string } },
		{ "operative_value$flex", { "userdata", flex_value } },
		{ "operative_type$flex", {
			"handler",       flex_value,
			"userdata_type", flex_value,
		} },
		-- ordinary data
		{ "tuple_value$flex", { "elements", array(flex_value) } },
		{ "tuple_type$flex", { "desc", flex_value } },
		{ "tuple_desc_type$flex", { "universe", flex_value } },
		{ "tuple_desc_concat_indep$stuck", { "prefix", flex_value, "suffix", flex_value}},
		{ "enum_value$flex", {
			"constructor", gen.builtin_string,
			"arg",         flex_value,
		} },
		{ "enum_type$flex", { "desc", flex_value } },
		{ "enum_desc_type$flex", { "universe", flex_value } },
		{ "enum_desc_value$flex", { "variants", gen.declare_map(gen.builtin_string, flex_value) } },
		{ "record_value$flex", { "fields", map(gen.builtin_string, flex_value) } },
		{ "record_type$flex", { "desc", flex_value } },
		{ "record_desc_type$flex", { "universe", flex_value } },
		{ "record_desc_value$flex", { "fields", map(gen.builtin_string, flex_value)}},
		{ "record_extend$stuck", {
			"base",      stuck_value,
			"extension", map(gen.builtin_string, flex_value),
		}, },
		-- Not used yet
		{ "object_value$flex", {
			"methods", map(gen.builtin_string, typed_term),
			"capture", flex_runtime_context_type,
		}, },
		{ "object_type$flex", { "desc", flex_value } },

		{ "star$strict", { "level", gen.builtin_integer, "depth", gen.builtin_integer } },
		{ "prop$strict", { "level", gen.builtin_integer } },

		{ "host_value$strict", { "host_value", gen.any_lua_type } },
		-- foreign data
		{ "host_type_type$strict" },
		{ "host_number_type$strict" },
		{ "host_int_fold$stuck", { "num", stuck_value, "f", flex_value, "acc", flex_value}},
		{ "host_bool_type$strict" },
		{ "host_string_type$strict" },
		{ "host_function_type$flex", {
			"param_type",  flex_value, -- must be a host_tuple_type
			-- host functions can only have explicit arguments
			"result_type", flex_value, -- must be a host_tuple_type
			"result_info", flex_value,
		}, },
		{ "host_wrapped_type$flex", { "type", flex_value } },
		{ "host_unstrict_wrapped_type$flex", { "type", flex_value } },
		{ "host_user_defined_type$flex", {
			"id",          host_user_defined_id,
			"family_args", array(flex_value),
		}, },
		{ "host_nil_type$strict" },
		--NOTE: host_tuple is not considered a host type because it's not a first class value in lua.
		{ "host_tuple_value$strict", { "elements", array(gen.any_lua_type) } },
		{ "host_tuple_type$flex", { "desc", flex_value } }, -- just like an ordinary tuple type but can only hold host_values

		-- a type family, that takes a type and a value, and produces a new type
		-- inhabited only by that single value and is a subtype of the type.
		-- example: singleton(integer, 5) is the type that is inhabited only by the
		-- number 5. values of this type can be, for example, passed to a function
		-- that takes any integer.
		-- alternative names include:
		-- - Most Specific Type (from discussion with open),
		-- - Val (from julia)
		{ "singleton$flex", {
			"supertype", flex_value,
			"value",     flex_value,
		} },
		{ "program_end$flex", { "result", flex_value } },
		{ "program_cont$flex", {
			"action",       unique_id,
			"argument",     flex_value,
			"continuation", flex_continuation,
		}, },

		{ "effect_elem$strict", { "tag", effect_id } },
		{ "effect_type$strict" },
		{ "effect_row$strict", {
			"components", set(unique_id),
		} },
		{ "effect_row_extend$stuck", {
			"base", flex_value,
			"rest", flex_value,
		} },
		{ "effect_row_type$strict" },

		{ "program_type$flex", {
			"effect_sig", flex_value,
			"base_type",  flex_value,
		} },
		{ "srel_type$flex", { "target_type", flex_value } },
		{ "variance_type$flex", { "target_type", flex_value } },
		{ "intersection_type$flex", {
			"left",  flex_value,
			"right", flex_value,
		} },
		{ "union_type$flex", {
			"left",  flex_value,
			"right", flex_value,
		} },

		{ "free$stuck", { "free", free } },
		{ "application$stuck", {
			"f",   stuck_value,
			"arg", flex_value,
		} },
		-- { "enum_elim_stuck", {
		-- 	"mechanism", value,
		-- 	"subject",   stuck_value,
		-- } },
		-- { "enum_rec_elim_stuck", {
		-- 	"handler", value,
		-- 	"subject", stuck_value,
		-- } },
		-- { "object_elim_stuck", {
		-- 	"mechanism", value,
		-- 	"subject",   stuck_value,
		-- } },
		{ "tuple_element_access$stuck", {
			"subject", stuck_value,
			"index",   gen.builtin_integer,
		} },
		{ "record_field_access$stuck", {
			"subject",    stuck_value,
			"field_name", gen.builtin_string,
		}, },
		{ "host_application$stuck", {
			"function", gen.any_lua_type,
			"arg",      stuck_value,
		} },
		{ "host_tuple$stuck", {
			"leading",       array(gen.any_lua_type),
			"stuck_element", stuck_value,
			"trailing",      array(flex_value), -- either host or neutral
		}, },
		{ "host_if$stuck", {
			"subject",    stuck_value,
			"consequent", flex_value,
			"alternate",  flex_value,
		}, },
		{ "host_intrinsic$stuck", {
			"source",       stuck_value,
			"start_anchor", anchor_type,
		} },
		{ "host_wrap$stuck", { "content", stuck_value } },
		{ "host_unwrap$stuck", { "container", stuck_value } },
	},
	function(_)
		local orig_host_value_constructor = strict_value.host_value
		local function host_value_constructor_check(val)
			-- Absolutely do not ever put a flex_value or stuck_value into here
			if stuck_value.value_check(val) or flex_value.value_check(val) then
				error("Tried to put flex or stuck value into strict_value.host_value!" .. tostring(val))
			end
			return U.notail(orig_host_value_constructor(val))
		end
		strict_value.host_value = host_value_constructor_check

		local orig_host_tuple_value_constructor = strict_value.host_tuple_value
		local function host_tuple_value_constructor_check(val)
			-- Absolutely do not ever put a flex_value or stuck_value into here
			for _, v in ipairs(val) do
				if stuck_value.value_check(v) or flex_value.value_check(v) then
					error("Tried to put flex or stuck value into strict_value.host_tuple_value!" .. tostring(v))
				end
			end

			return U.notail(orig_host_tuple_value_constructor(val))
		end
		strict_value.host_tuple_value = host_tuple_value_constructor_check
	end
)

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

-- metavariables are unique (typechecker state increments after each mv constructed)
-- anchors are unique (their constructor is already memoized)
-- runtime and typechecking contexts are immutable (or at least not intended to be mutated)
-- host user defined ids are unique (identified by identity, not by name)
-- subtype relations are unique (all instances are either individual
-- or constructed from FunctionRelation, which is already memoized)
for _, t in ipairs {
	metavariable_type,
	anchor_type,
	span_type,
	flex_runtime_context_type,
	strict_runtime_context_type,
	typechecking_context_type,
	host_user_defined_id,
	SubtypeRelation,
} do
	traits.freeze:implement_on(t, {
		freeze = function(_, val)
			return val
		end,
	})
end

local host_syntax_type = strict_value.host_user_defined_type({ name = "syntax" }, array(strict_value)())
local host_environment_type = strict_value.host_user_defined_type({ name = "environment" }, array(strict_value)())
local host_typed_term_type = strict_value.host_user_defined_type({ name = "typed_term" }, array(strict_value)())
local host_goal_type = strict_value.host_user_defined_type({ name = "goal" }, array(strict_value)())
local host_inferrable_term_type =
	strict_value.host_user_defined_type({ name = "inferrable_term" }, array(strict_value)())
local host_checkable_term_type = strict_value.host_user_defined_type({ name = "checkable_term" }, array(strict_value)())
local host_purity_type = strict_value.host_user_defined_type({ name = "purity" }, array(strict_value)())
local host_block_purity_type = strict_value.host_user_defined_type({ name = "block_purity" }, array(strict_value)())
-- return ok, err
local host_lua_error_type = strict_value.host_user_defined_type({ name = "lua_error_type" }, array(strict_value)())

---@class DescConsContainer
local DescCons = --[[@enum DescCons]]
	{
		cons = "cons",
		empty = "empty",
	}

local typed_term_array = array(typed_term)
local anchored_inferrable_term_array = array(anchored_inferrable_term)
local unanchored_inferrable_term_array = array(unanchored_inferrable_term)
local flex_value_array = array(flex_value)
local strict_value_array = array(strict_value)
local stuck_value_array = array(stuck_value)
local spanned_name_array = array(spanned_name)

---@param ... flex_value
---@return flex_value
local function tup_val(...)
	return U.notail(flex_value.tuple_value(flex_value_array(...)))
end

---@param prefix flex_value
---@param next_elem flex_value
---@return flex_value
---@diagnostic disable-next-line: incomplete-signature-doc
local function cons(prefix, next_elem, ...)
	if select("#", ...) > 0 then
		error(("%d extra arguments passed to terms.cons"):format(select("#", ...)))
	end
	return U.notail(flex_value.enum_value(DescCons.cons, tup_val(prefix, next_elem)))
end

local empty = flex_value.enum_value(DescCons.empty, tup_val())

---@param desc flex_value `flex_value.enum_value(DescCons.cons, …))`
---@return flex_value prefix
---@return flex_value next_elem
local function uncons(desc)
	local constructor, arg = desc:unwrap_enum_value()
	if constructor ~= DescCons.cons then
		error(string.format("expected constructor DescCons.cons, got %s: %s", s(constructor), s(desc)))
	end
	local elements = arg:unwrap_tuple_value()
	if elements:len() ~= 2 then
		error(
			string.format("enum_value with constructor DescCons.cons should have 2 args, but has %s", s(elements:len()))
		)
	end
	return elements[1], elements[2]
end

---@param desc flex_value `flex_value.enum_value(DescCons.empty, …))`
local function unempty(desc)
	local constructor = desc:unwrap_enum_value()
	if constructor ~= DescCons.empty then
		error(string.format("expected constructor DescCons.empty, got %s: %s", s(constructor), s(desc)))
	end
end

---@param ... flex_value
---@return flex_value
local function tuple_desc(...)
	local a = empty
	for i = 1, select("#", ...) do
		local e = select(i, ...)
		if e ~= nil then
			a = cons(a, e)
		end
	end
	return a
end

---@param ... strict_value
---@return strict_value
local function strict_tup_val(...)
	return U.notail(strict_value.tuple_value(strict_value_array(...)))
end

---@param prefix strict_value
---@param next_elem strict_value
---@return strict_value
---@diagnostic disable-next-line: incomplete-signature-doc
local function strict_cons(prefix, next_elem, ...)
	if select("#", ...) > 0 then
		error(("%d extra arguments passed to terms.strict_cons"):format(select("#", ...)))
	end
	return U.notail(strict_value.enum_value(DescCons.cons, strict_tup_val(prefix, next_elem, ...)))
end

local strict_empty = empty:unwrap_strict()

---@param ... strict_value
---@return strict_value
local function strict_tuple_desc(...)
	local a = strict_empty
	for i = 1, select("#", ...) do
		local e = select(i, ...)
		if e ~= nil then
			a = strict_cons(a, e)
		end
	end
	return a
end

---@param start_anchor Anchor
---@param prefix anchored_inferrable
---@param debug_prefix spanned_name
---@param next_elem anchored_inferrable
---@param debug_next_elem spanned_name
---@return anchored_inferrable `anchored_inferrable_term(unanchored_inferrable_term.enum_cons(DescCons.cons, anchored_inferrable_term(unanchored_inferrable_term.tuple_cons(…))))`
---@diagnostic disable-next-line: incomplete-signature-doc
local function inferrable_cons(start_anchor, prefix, debug_prefix, next_elem, debug_next_elem, ...)
	if select("#", ...) > 0 then
		error(("%d extra arguments passed to terms.inferrable_cons"):format(select("#", ...)))
	end
	return U.notail(
		anchored_inferrable_term(
			start_anchor,
			unanchored_inferrable_term.enum_cons(
				DescCons.cons,
				anchored_inferrable_term(
					start_anchor,
					unanchored_inferrable_term.tuple_cons(
						anchored_inferrable_term_array(prefix, next_elem),
						spanned_name_array(debug_prefix, debug_next_elem)
					)
				)
			)
		)
	)
end

local inferrable_empty = anchored_inferrable_term(
	format.anchor_here(),
	unanchored_inferrable_term.enum_cons(
		DescCons.empty,
		anchored_inferrable_term(
			format.anchor_here(),
			unanchored_inferrable_term.tuple_cons(anchored_inferrable_term_array(), spanned_name_array())
		)
	)
)
local debug_inferrable_empty = spanned_name("terms.inferrable_empty", format.span_here())

---@param start_anchor Anchor
---@param ... (anchored_inferrable | spanned_name) (`anchored_inferrable`, `spanned_name`)\*
---@return anchored_inferrable
local function inferrable_tuple_desc(start_anchor, ...)
	local a = inferrable_empty
	local debug_a = debug_inferrable_empty
	local span = format.span_here(2)
	for i = 1, select("#", ...), 2 do
		local e, debug_e = select(i, ...), select(i + 1, ...)
		if e ~= nil then
			if debug_e == nil then
				error(("inferrable_tuple_desc: missing spanned_name at argument %d"):format(i + 1))
			end
			a, debug_a =
				inferrable_cons(start_anchor, a, debug_a, e, debug_e),
				spanned_name(("terms.inferrable_tuple_desc.varargs[%d]"):format(i), span)
		end
	end
	return a
end

---@param prefix typed
---@param next_elem typed
---@return typed `typed_term.enum_cons(DescCons.cons, typed_term.tuple_cons(…))`
---@diagnostic disable-next-line: incomplete-signature-doc
local function typed_cons(prefix, next_elem, ...)
	if select("#", ...) > 0 then
		error(("%d extra arguments passed to terms.typed_cons"):format(select("#", ...)))
	end
	return U.notail(typed_term.enum_cons(DescCons.cons, typed_term.tuple_cons(typed_term_array(prefix, next_elem))))
end

local typed_empty = typed_term.enum_cons(DescCons.empty, typed_term.tuple_cons(typed_term_array()))

---@param ... typed
---@return typed
local function typed_tuple_desc(...)
	local a = typed_empty
	for i = 1, select("#", ...) do
		local e = select(i, ...)
		if e ~= nil then
			a = typed_cons(a, e)
		end
	end
	return a
end

---@class RecordDescConsContainer
local RecordDescCons = --[[@enum RecordDescCons]]
	{
		cons = "cons",
		empty = "empty",
	}

---@param desc flex_value `flex_value.enum_value(RecordDescCons.cons, …))`
---@return flex_value field_descs
---@return flex_value name_something
---@return flex_value f
local function record_uncons(desc)
	local constructor, arg = desc:unwrap_enum_value()
	if constructor ~= RecordDescCons.cons then
		error(string.format("expected constructor RecordDescCons.cons, got %s: %s", s(constructor), s(desc)))
	end
	local elements = arg:unwrap_tuple_value()
	if elements:len() ~= 3 then
		error(
			string.format(
				"enum_value with constructor RecordDescCons.cons should have 3 args, but has %s",
				s(elements:len())
			)
		)
	end
	return elements[1], elements[2], elements[3]
end

---@param desc flex_value `flex_value.enum_value(RecordDescCons.empty, …))`
local function record_unempty(desc)
	local constructor = desc:unwrap_enum_value()
	if constructor ~= DescCons.empty then
		error(string.format("expected constructor RecordDescCons.empty, got %s: %s", s(constructor), s(desc)))
	end
end

---@module "types.tristate"
local tristate = gen.declare_enum("tristate", {
	{ "success" },
	{ "continue" },
	{ "failure" },
})

local unique_id_set = set(unique_id)

local unit_type = strict_value.tuple_type(empty:unwrap_strict())
local unit_val = strict_tup_val()
local effect_registry = new_registry("effect")
local TCState =
	effect_id(effect_registry:register("TCState", "effects that manipulate the typechecker state"), unique_id_set())
local lua_prog = effect_id(effect_registry:register("lua_prog", "running effectful lua code"), unique_id_set())

local terms = {
	metavariable_mt = metavariable_mt,
	checkable_term = checkable_term, -- {}
	anchored_inferrable_term = anchored_inferrable_term, -- {}
	anchored_inferrable_term_array = anchored_inferrable_term_array, -- {}
	unanchored_inferrable_term = unanchored_inferrable_term, -- {}
	typed_term = typed_term, -- {}
	typed_term_array = typed_term_array,
	free = free,
	visibility = visibility,
	purity = purity,
	block_purity = block_purity,
	result_info = result_info,
	flex_value = flex_value,
	flex_value_array = flex_value_array,
	strict_value = strict_value,
	strict_value_array = strict_value_array,
	stuck_value = stuck_value,
	stuck_value_array = stuck_value_array,
	binding = binding,
	expression_goal = expression_goal,
	host_syntax_type = host_syntax_type,
	host_environment_type = host_environment_type,
	host_typed_term_type = host_typed_term_type,
	host_goal_type = host_goal_type,
	host_inferrable_term_type = host_inferrable_term_type,
	host_checkable_term_type = host_checkable_term_type,
	host_purity_type = host_purity_type,
	host_block_purity_type = host_block_purity_type,
	host_lua_error_type = host_lua_error_type,
	unique_id = unique_id,
	unique_id_set = unique_id_set,
	spanned_name = spanned_name,
	spanned_name_array = spanned_name_array,

	flex_runtime_context = flex_runtime_context,
	strict_runtime_context = strict_runtime_context,
	typechecking_context = typechecking_context,
	module_mt = module_mt,
	strict_runtime_context_type = strict_runtime_context_type,
	flex_runtime_context_type = flex_runtime_context_type,
	typechecking_context_type = typechecking_context_type,
	subtype_relation_mt = subtype_relation_mt,
	SubtypeRelation = SubtypeRelation,
	constraintelem = constraintelem,
	constraintcause = constraintcause,

	DescCons = DescCons,
	tup_val = tup_val,
	cons = cons,
	empty = empty,
	uncons = uncons,
	unempty = unempty,
	tuple_desc = tuple_desc,
	strict_tup_val = strict_tup_val,
	strict_cons = strict_cons,
	strict_empty = strict_empty,
	strict_tuple_desc = strict_tuple_desc,
	typed_cons = typed_cons,
	typed_empty = typed_empty,
	typed_tuple_desc = typed_tuple_desc,
	inferrable_cons = inferrable_cons,
	inferrable_empty = inferrable_empty,
	inferrable_tuple_desc = inferrable_tuple_desc,
	RecordDescCons = RecordDescCons,
	record_empty = record_empty,
	record_uncons = record_uncons,
	unit_type = unit_type,
	unit_val = unit_val,
	effect_id = effect_id,
	flex_continuation = flex_continuation,
	strict_continuation = strict_continuation,
	stuck_continuation = stuck_continuation,

	effect_registry = effect_registry,
	TCState = TCState,
	lua_prog = lua_prog,
	verify_placeholders = verify_placeholders,
	verify_placeholder_lite = verify_placeholder_lite,

	tristate = tristate,
}

local override_prettys = require "terms-pretty"(terms)
local checkable_term_override_pretty = override_prettys.checkable_term_override_pretty
local unanchored_inferrable_term_override_pretty = override_prettys.unanchored_inferrable_term_override_pretty
local typed_term_override_pretty = override_prettys.typed_term_override_pretty
local flex_value_override_pretty = override_prettys.flex_value_override_pretty
local stuck_value_override_pretty = override_prettys.stuck_value_override_pretty
local binding_override_pretty = override_prettys.binding_override_pretty
local spanned_name_override_pretty = override_prettys.spanned_name_override_pretty

checkable_term:derive(derivers.pretty_print, checkable_term_override_pretty)
anchored_inferrable_term:derive(derivers.pretty_print)
unanchored_inferrable_term:derive(derivers.pretty_print, unanchored_inferrable_term_override_pretty)
typed_term:derive(derivers.pretty_print, typed_term_override_pretty)
visibility:derive(derivers.pretty_print)
free:derive(derivers.pretty_print)
flex_value:derive(derivers.pretty_print, flex_value_override_pretty)
strict_value:derive(derivers.pretty_print, flex_value_override_pretty)
stuck_value:derive(derivers.pretty_print, flex_value_override_pretty)
binding:derive(derivers.pretty_print, binding_override_pretty)
expression_goal:derive(derivers.pretty_print)
spanned_name:derive(derivers.pretty_print, spanned_name_override_pretty)
purity:derive(derivers.pretty_print)
result_info:derive(derivers.pretty_print)
constraintcause:derive(derivers.pretty_print)
flex_continuation:derive(derivers.pretty_print)
strict_continuation:derive(derivers.pretty_print)
stuck_continuation:derive(derivers.pretty_print)

local glsl_print = require "glsl-print"
typed_term:derive(glsl_print.glsl_print_deriver, glsl_print.typed_term_glsl)
local pretty_printer = require "pretty-printer"
typed_term.methods.glsl_print = pretty_printer.glsl_print

local internals_interface = require "internals-interface"
internals_interface.terms = terms
return setmetatable(terms, {
	__index = function(_, k)
		error(debug.traceback("'" .. k .. "' doesn't exist in terms!"))
	end,
})
