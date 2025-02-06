-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>
local fibbuf = require "fibonacci-buffer"
local gen = require "terms-generators"
local U = require "alicorn-utils"
local pretty_printer = require "pretty-printer"
local tostring = tostring
---@module "terms".typechecking_context_type
local typechecking_context_type
---@module "terms".strict_runtime_context_type
local strict_runtime_context_type
---@module "terms".flex_runtime_context_type
local flex_runtime_context_type
---@module "terms".DescCons
local DescCons

-- stylua: ignore start

---@module "pretty-printer".PrettyPrint
do local PrettyPrint end

---@module "types.binding"
do local _ end
---@module "types.checkable"
do local _ end
---@module "types.unanchored_inferrable"
do local _ end
---@module "types.typed"
do local _ end
---@module "types.strict_value"
do local _ end
---@module "types.flex_value"
do local _ end
---@module "types.stuck_value"
do local _ end
---@module "types.var_debug"
do local _ end

-- stylua: ignore end

---@param self EnumValue
---@param name string
---@return string name
local function enum_name(self, name)
	return ("%s.%s"):format(getmetatable(self)._name, name)
end

pretty_printer.hidden_fields.capture = function(capture)
	if capture._record == nil and capture.bindings and capture.bindings.len then
		local prefix = ""
		if strict_runtime_context_type.value_check(capture) then
			prefix = "strict "
		end
		if flex_runtime_context_type.value_check(capture) then
			prefix = "flex "
		end
		-- FIXME: we can't print all the bindings for a capture currently because we
		-- capture everything in scope and that's way too verbose
		-- if that gets fixed to only capture used bindings we can print more
		-- local ret = {}
		-- for i = 1, capture.bindings:len() do
		-- 	ret[i] = capture.bindings:get(i)
		-- end
		-- return ret
		return prefix .. "runtime context with len=" .. tostring(capture.bindings:len())
	end
	return capture
end

-- pretty printing context stuff

local prettyprinting_context_mt = {}
local prettyprinting_context_redirecting_mt = {}

---@class PrettyPrintingContext
---@field bindings FibonacciBuffer
local PrettyprintingContext = {}

---@return PrettyPrintingContext
function PrettyprintingContext.new()
	local self = {}
	self.bindings = fibbuf()
	return setmetatable(self, prettyprinting_context_mt)
end

---@param context TypecheckingContext
---@return PrettyPrintingContext
function PrettyprintingContext.from_typechecking_context(context)
	return setmetatable({
		prettyprinting_context_from = function(self)
			local context = self.prettyprinting_context_redirect
			setmetatable(self, prettyprinting_context_mt)
			self.bindings = context.bindings
		end,
		prettyprinting_context_redirect = context,
	}, prettyprinting_context_redirecting_mt)
end

---@param context StrictRuntimeContext
---@return PrettyPrintingContext
function PrettyprintingContext.from_strict_runtime_context(context)
	return setmetatable({
		prettyprinting_context_from = function(self)
			local context = self.prettyprinting_context_redirect
			setmetatable(self, prettyprinting_context_mt)
			self.bindings = context.bindings
		end,
		prettyprinting_context_redirect = context,
	}, prettyprinting_context_redirecting_mt)
end

---@param context FlexRuntimeContext
---@return PrettyPrintingContext
function PrettyprintingContext.from_flex_runtime_context(context)
	return setmetatable({
		prettyprinting_context_from = function(self)
			local context = self.prettyprinting_context_redirect
			setmetatable(self, prettyprinting_context_mt)
			self.bindings = context.bindings
		end,
		prettyprinting_context_redirect = context,
	}, prettyprinting_context_redirecting_mt)
end

---@param index integer
---@return string
function PrettyprintingContext:get_name(index)
	local binding = self.bindings:get(index)
	if binding == nil then
		return nil
	end
	return binding.name
end

---@param index integer
---@return var_debug?
function PrettyprintingContext:get_var_debug(index)
	local binding = self.bindings:get(index)
	if binding == nil then
		return nil
	end
	return binding.debuginfo
end

---@param name string
---@return PrettyPrintingContext
function PrettyprintingContext:append(name)
	if type(name) ~= "string" then
		error("PrettyprintingContext:append must append string name")
	end
	local copy = {}
	copy.bindings = self.bindings:append({ name = name })
	return setmetatable(copy, prettyprinting_context_mt)
end

function PrettyprintingContext:len()
	return self.bindings:len()
end

prettyprinting_context_mt.__index = PrettyprintingContext
prettyprinting_context_mt.__len = PrettyprintingContext.len
function prettyprinting_context_mt:__tostring()
	return "PrettyprintingContext with " .. self.bindings:len() .. " bindings."
end

function prettyprinting_context_redirecting_mt:__index(k)
	if k == "append" then
		return self:prettyprinting_context_from().append
	end
	return self.prettyprinting_context_redirect[k]
end

function prettyprinting_context_redirecting_mt:__newindex(k, v)
	self.prettyprinting_context_redirect[k] = v
end

function prettyprinting_context_redirecting_mt:__call(...)
	return self.prettyprinting_context_redirect(...)
end

function prettyprinting_context_redirecting_mt:__len()
	return #self.prettyprinting_context_redirect
end

function prettyprinting_context_redirecting_mt:__tostring()
	return tostring(self.prettyprinting_context_redirect)
end

local prettyprinting_context_metatable_equality = gen.metatable_equality(prettyprinting_context_mt)
local prettyprinting_context_redirecting_metatable_equality =
	gen.metatable_equality(prettyprinting_context_redirecting_mt)
local prettyprinting_context_type = gen.declare_foreign(function(val)
	return prettyprinting_context_metatable_equality(val) or prettyprinting_context_redirecting_metatable_equality(val)
end, "PrettyPrintingContext")

---@alias AnyContext PrettyPrintingContext | TypecheckingContext | StrictRuntimeContext | FlexRuntimeContext

---@param context AnyContext
---@return PrettyPrintingContext
local function ensure_context(context)
	if prettyprinting_context_type.value_check(context) == true then
		---@cast context PrettyPrintingContext
		return context
	elseif typechecking_context_type.value_check(context) == true then
		---@cast context TypecheckingContext
		return PrettyprintingContext.from_typechecking_context(context)
	elseif strict_runtime_context_type.value_check(context) == true then
		---@cast context StrictRuntimeContext
		return PrettyprintingContext.from_strict_runtime_context(context)
	elseif flex_runtime_context_type.value_check(context) == true then
		---@cast context FlexRuntimeContext
		return PrettyprintingContext.from_flex_runtime_context(context)
	elseif
		context ~= nil
		and context._record == nil
		and context.as_strict ~= nil
		and strict_runtime_context_type.value_check(context:as_strict()) == true
	then
		context = context:as_strict()
		return PrettyprintingContext.from_strict_runtime_context(context)
	elseif
		context ~= nil
		and context._record == nil
		and context.as_strict ~= nil
		and flex_runtime_context_type.value_check(context:as_strict()) == true
	then
		context = context:as_strict()
		return PrettyprintingContext.from_flex_runtime_context(context)
	elseif
		context ~= nil
		and context._record == nil
		and context.as_flex ~= nil
		and flex_runtime_context_type.value_check(context:as_flex()) == true
	then
		context = context:as_flex()
		return PrettyprintingContext.from_flex_runtime_context(context)
	else
		--print("!!!!!!!!!! MISSING PRETTYPRINTER CONTEXT !!!!!!!!!!!!!!")
		--print("making something up")
		return PrettyprintingContext.new():append("#made-up")
	end
end

-- generic helper functions

---@param pp PrettyPrint
---@param name string
---@param debuginfo var_debug
---@param expr unanchored_inferrable | typed
---@param context PrettyPrintingContext
---@return PrettyPrintingContext
local function let_helper(pp, name, debuginfo, expr, context)
	pp:unit(name)
	pp:any(debuginfo, context)

	pp:unit(pp:set_color())
	pp:unit(" = ")
	pp:unit(pp:reset_color())

	pp:_indent()
	pp:any(expr, context)
	pp:_dedent()

	context = context:append(name)

	return context
end

---@param pp PrettyPrint
---@param names ArrayValue<string>
---@param debuginfo var_debug,
---@param subject unanchored_inferrable | typed
---@param context PrettyPrintingContext
---@return PrettyPrintingContext
local function tuple_elim_helper(pp, names, debuginfo, subject, context)
	local inner_context = context

	pp:unit(pp:set_color())
	pp:unit("(")
	pp:unit(pp:reset_color())

	for i, name in ipairs(names) do
		inner_context = inner_context:append(name)

		if i > 1 then
			pp:unit(pp:set_color())
			pp:unit(", ")
			pp:unit(pp:reset_color())
		end

		pp:unit(name)
	end

	pp:unit(pp:set_color())
	pp:unit(")")
	pp:any(debuginfo, context)
	pp:unit(" = ")
	pp:unit(pp:reset_color())

	pp:any(subject, context)

	return inner_context
end

---@class (exact) TupleDescFlat
---@field [1] ArrayValue
---@field [2] unanchored_inferrable | typed
---@field [3] PrettyPrintingContext

---@param pp PrettyPrint
---@param members TupleDescFlat[]
---@param names ArrayValue?
local function tuple_type_helper(pp, members, names)
	local m = #members

	if m == 0 then
		return
	end

	if not names then
		-- get them from last (outermost) desc
		-- the name of the last member is lost in this case
		names = members[m][1]
	end

	local n = type(names) == "table" and names:len() or 0

	for i, mem in ipairs(members) do
		if i > 1 then
			pp:unit(" ")
		end

		pp:unit(pp:set_color())
		pp:unit("(")
		pp:unit(pp:reset_color())

		if i > n then
			pp:unit(string.format("#unk%d", i))
		else
			pp:unit(names[i])
		end

		pp:unit(pp:set_color())
		pp:unit(" : ")
		pp:unit(pp:reset_color())

		pp:any(mem[2], mem[3])

		pp:unit(pp:set_color())
		pp:unit(")")
		pp:unit(pp:reset_color())
	end
end

---@overload fun(term: unanchored_inferrable): boolean, anchored_inferrable
---@generic T
---@param term T
---@return boolean
---@return T?
local function as_any_tuple_type(term)
	---@cast term unanchored_inferrable|flex_value|typed
	local ok, desc = term:as_tuple_type()
	if ok then
		return ok, desc
	end

	ok, desc = term:as_host_tuple_type()
	if ok then
		return ok, desc
	end

	return false
end

-- unfortunately not generic helper functions

---@param pp PrettyPrint
---@param term unanchored_inferrable
---@param context PrettyPrintingContext
local function inferrable_let_or_tuple_elim(pp, term, context)
	pp:_enter()

	local name, debuginfo, expr, names, subject
	while true do
		if term:is_let() then
			name, debuginfo, expr, term = term:unwrap_let()
			_, term = term:unwrap_anchored_inferrable()
			_, expr = expr:unwrap_anchored_inferrable()

			-- rear-loading prefix to cheaply handle first loop not needing prefix
			pp:unit(pp:set_color())
			pp:unit(enum_name(term, "let "))
			pp:unit(pp:reset_color())
			context = let_helper(pp, name, debuginfo, expr, context)
			pp:unit("\n")
			pp:_prefix()
		elseif term:is_tuple_elim() then
			names, debuginfo, subject, term = term:unwrap_tuple_elim()
			_, subject = subject:unwrap_anchored_inferrable()
			_, term = term:unwrap_anchored_inferrable()

			pp:unit(pp:set_color())
			pp:unit(enum_name(term, "tuple_elim "))
			pp:unit(pp:reset_color())
			context = tuple_elim_helper(pp, names, debuginfo, subject, context)
			pp:unit("\n")
			pp:_prefix()
		else
			break
		end
	end

	pp:any(term, context)

	pp:_exit()
end

---@param pp PrettyPrint
---@param term typed
---@param context PrettyPrintingContext
local function typed_let_or_tuple_elim(pp, term, context)
	pp:_enter()

	local name, expr, names, subject
	while true do
		if term:is_let() then
			name, debuginfo, expr, term = term:unwrap_let()

			-- rear-loading prefix to cheaply handle first loop not needing prefix
			pp:unit(pp:set_color())
			pp:unit(enum_name(term, "let "))
			pp:unit(pp:reset_color())
			context = let_helper(pp, name, debuginfo, expr, context)
			pp:unit("\n")
			pp:_prefix()
		elseif term:is_tuple_elim() then
			names, debuginfo, subject, _, term = term:unwrap_tuple_elim()

			pp:unit(pp:set_color())
			pp:unit(enum_name(term, "tuple_elim "))
			pp:unit(pp:reset_color())
			context = tuple_elim_helper(pp, names, debuginfo, subject, context)
			pp:unit("\n")
			pp:_prefix()
		else
			break
		end
	end

	pp:any(term, context)

	pp:_exit()
end

---@param term anchored_inferrable
---@param context PrettyPrintingContext
---@return boolean
---@return boolean
---@return (string | ArrayValue)?
---@return unanchored_inferrable
---@return PrettyPrintingContext
local function inferrable_destructure_helper(term, context)
	local _, term = term:unwrap_anchored_inferrable()

	if term:is_let() then
		-- destructuring with a let effectively just renames the parameter
		-- thus it's usually superfluous to write code like this
		-- and probably unwise to elide the let
		-- but some operatives that are generic over lets and tuple-elims do this
		-- e.g. forall, lambda
		-- so we pretty this anyway
		local name, debuginfo, expr, body = term:unwrap_let()
		local _, expr = expr:unwrap_anchored_inferrable()
		local _, body = body:unwrap_anchored_inferrable()
		local ok, index, info = expr:as_bound_variable()
		local is_destructure = ok and index == context:len()
		if is_destructure then
			context = context:append(name)
			return true, true, name, body, context
		end
	elseif term:is_tuple_elim() then
		local names, debuginfo, subject, body = term:unwrap_tuple_elim()
		local _, subject = subject:unwrap_anchored_inferrable()
		local _, body = body:unwrap_anchored_inferrable()
		local ok, index, info = subject:as_bound_variable()
		local is_destructure = ok and index == context:len()
		if is_destructure then
			for _, name in names:ipairs() do
				context = context:append(name)
			end
			return true, false, names, body, context
		end
	end
	return false, false, nil, term, context
end

---@param term typed
---@param context PrettyPrintingContext
---@param capture flex_value
---@return boolean
---@return boolean
---@return (string | ArrayValue)?
---@return typed
---@return PrettyPrintingContext
local function typed_destructure_helper(term, context, capture)
	if term:is_let() then
		-- destructuring with a let effectively just renames the parameter
		-- thus it's usually superfluous to write code like this
		-- and probably unwise to elide the let
		-- but some operatives that are generic over lets and tuple-elims do this
		-- e.g. forall, lambda
		-- so we pretty this anyway
		local name, debuginfo, expr, body = term:unwrap_let()
		local ok, index, info = expr:as_bound_variable()
		local is_destructure = ok and index == context:len()
		if is_destructure then
			context = context:append(name)
			return is_destructure, true, name, body, context
		end
	elseif term:is_tuple_elim() then
		local names, debuginfo, subject, _, body = term:unwrap_tuple_elim()
		local ok, index, info = subject:as_bound_variable()
		local is_destructure = ok and index == context:len()
		if is_destructure then
			for _, name in names:ipairs() do
				context = context:append(name)
			end
			return is_destructure, false, names, body, context
		end
	end
	return false, false, nil, term, context
end

---@param desc anchored_inferrable
---@param context PrettyPrintingContext
---@return boolean
---@return TupleDescFlat[]?
---@return integer?
local function inferrable_tuple_type_flatten(desc, context)
	local _, desc = desc:unwrap_anchored_inferrable()
	local ok, constructor, arg = desc:as_enum_cons()
	if not ok then
		return false
	end
	if constructor == DescCons.empty then
		return true, {}, 0
	elseif constructor == DescCons.cons then
		local _, arg = arg:unwrap_anchored_inferrable()
		local ok, elements, info = arg:as_tuple_cons()
		if not ok or elements:len() ~= 2 then
			return false
		end
		local desc = elements[1]
		local _, f = elements[2]:unwrap_anchored_inferrable()
		local ok, param_name, _, body, _ = f:as_annotated_lambda()
		if not ok then
			return false
		end
		local inner_context = context:append(param_name)
		local _, _, names, body, inner_context = inferrable_destructure_helper(body, inner_context)
		---@cast names ArrayValue
		local ok, prev, n = inferrable_tuple_type_flatten(desc, context)
		if not ok then
			return false
		end
		n = n + 1
		prev[n] = { names, body, inner_context }
		return true, prev, n
	else
		return false
	end
end

---@param desc typed
---@param context PrettyPrintingContext
---@return boolean
---@return TupleDescFlat[]?
---@return integer?
local function typed_tuple_type_flatten(desc, context)
	local ok, constructor, arg = desc:as_enum_cons()
	if not ok then
		return false
	end
	if constructor == DescCons.empty then
		return true, {}, 0
	elseif constructor == DescCons.cons then
		local ok, elements = arg:as_tuple_cons()
		if not ok or elements:len() ~= 2 then
			return false
		end
		local desc = elements[1]
		local f = elements[2]
		local ok, param_name, param_debug, body, capture, capture_debug, start_anchor = f:as_lambda()
		if not ok then
			return false
		end
		local inner_context = context:append(param_name)
		local _, _, names, body, inner_context = typed_destructure_helper(body, inner_context, capture)
		---@cast names ArrayValue
		local ok, prev, n = typed_tuple_type_flatten(desc, context)
		if not ok then
			return false
		end
		n = n + 1
		prev[n] = { names, body, inner_context }
		return true, prev, n
	else
		return false
	end
end

---@param desc flex_value
---@return boolean
---@return TupleDescFlat[]?
---@return integer?
local function value_tuple_type_flatten(desc)
	local ok, constructor, arg = desc:as_enum_value()
	if not ok then
		return false
	end
	if constructor == DescCons.empty then
		return true, {}, 0
	elseif constructor == DescCons.cons then
		local ok, elements = arg:as_tuple_value()
		if not ok or elements:len() ~= 2 then
			return false
		end
		local desc = elements[1]
		local f = elements[2]
		local ok, param_name, code, capture, capture_debug, param_debug = f:as_closure()
		if not ok then
			return false
		end
		local context = PrettyprintingContext.new()
		context = context:append(capture_debug.name)
		context = context:append(param_name)
		local _, _, names, code, inner_context = typed_destructure_helper(code, context, capture)
		---@cast names ArrayValue
		local ok, prev, n = value_tuple_type_flatten(desc)
		if not ok then
			return false
		end
		n = n + 1
		prev[n] = { names, code, inner_context }
		return true, prev, n
	else
		return false
	end
end

-- pretty printing impls
-- helplessly copypasted in unhealthy quantities
-- maintainers beware

---@class BindingOverridePretty : binding
local binding_override_pretty = {}

---@class CheckableTermOverride : checkable
local checkable_term_override_pretty = {}

---@class FlexValueOverridePretty : flex_value
local flex_value_override_pretty = {}

---@class UnanchoredInferrableTermOverride : unanchored_inferrable
local unanchored_inferrable_term_override_pretty = {}

---@class StuckValueOverridePretty : stuck_value
local stuck_value_override_pretty = {}

---@class TypedTermOverride : typed
local typed_term_override_pretty = {}

---@param self var_debug
---@param pp PrettyPrint
---@param context AnyContext
local function var_debug_override_pretty(self, pp, context)
	local name, anchor = self:unwrap_var_debug()
	pp:unit(name)

	pp:unit(pp:set_color())
	pp:unit("🖉")

	pp:_enter()
	pp:any(anchor, context)
	pp:_exit()
	pp:unit(pp:reset_color())
end

---@param pp PrettyPrint
---@param context AnyContext
function checkable_term_override_pretty:inferrable(pp, context)
	local inferrable_term = self:unwrap_inferrable()
	context = ensure_context(context)
	pp:any(inferrable_term, context)
end

---@param pp PrettyPrint
---@param context AnyContext
function unanchored_inferrable_term_override_pretty:typed(pp, context)
	local type, _, typed_term = self:unwrap_typed()
	context = ensure_context(context)

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit(enum_name(self, "the ("))
	pp:unit(pp:reset_color())

	pp:any(type, context)

	pp:unit(pp:set_color())
	pp:unit(") (")
	pp:unit(pp:reset_color())

	pp:any(typed_term, context)

	pp:unit(pp:set_color())
	pp:unit(")")
	pp:unit(pp:reset_color())

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function typed_term_override_pretty:literal(pp, context)
	local literal_value = self:unwrap_literal()

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit("‹")
	pp:unit(pp:reset_color())

	pp:any(literal_value, context)

	pp:unit(pp:set_color())
	pp:unit("›")
	pp:unit(pp:reset_color())

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function unanchored_inferrable_term_override_pretty:bound_variable(pp, context)
	local index, debuginfo = self:unwrap_bound_variable()
	context = ensure_context(context)

	pp:_enter()

	if context:len() >= index then
		pp:unit(context:get_name(index))
	else
		-- TODO: warn on context too short?
		pp:unit(pp:set_color())
		pp:unit(enum_name(self, "bound_variable("))
		pp:unit(pp:reset_color())

		pp:unit(tostring(index))

		pp:unit(pp:set_color())
		pp:unit(", ")
		pp:unit(pp:reset_color())

		pp:any(debuginfo, context)

		pp:unit(pp:set_color())
		pp:unit(")")
		pp:unit(pp:reset_color())
	end

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function typed_term_override_pretty:bound_variable(pp, context)
	local index, var_dbg = self:unwrap_bound_variable()
	context = ensure_context(context)

	pp:_enter()

	print(tostring(context))
	local context_var_dbg = context:get_var_debug(index)
	if var_dbg ~= context_var_dbg then
		pp:unit(pp:set_color())
		pp:unit(enum_name(self, "bound_variable("))
		pp:unit(pp:reset_color())

		pp:any(index, context)

		pp:unit(pp:set_color())
		pp:unit("→(")
		pp:unit(pp:reset_color())

		pp:_enter()
		pp:any(context_var_dbg, context)
		pp:_exit()

		pp:unit(pp:set_color())
		pp:unit(" from ")
		pp:unit(pp:reset_color())

		pp:_enter()
		pp:unit(tostring(context)) -- intentional `tostring()`
		pp:_exit()

		pp:unit(pp:set_color())
		pp:unit("), ")
		pp:unit(pp:reset_color())

		pp:any(var_dbg, context)

		pp:unit(pp:set_color())
		pp:unit(")")
		pp:unit(pp:reset_color())
	elseif context:len() >= index then
		pp:unit(context:get_name(index))
	else
		-- TODO: warn on context too short?
		pp:unit(pp:set_color())
		pp:unit(enum_name(self, "bound_variable("))
		pp:unit(pp:reset_color())

		pp:unit(tostring(index))

		pp:unit(pp:set_color())
		pp:unit(", ")
		pp:unit(pp:reset_color())

		pp:any(var_dbg, context)

		pp:unit(pp:set_color())
		pp:unit(")")
		pp:unit(pp:reset_color())
	end

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function binding_override_pretty:let(pp, context)
	local name, debuginfo, expr = self:unwrap_let()
	context = ensure_context(context)

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit(enum_name(self, "let "))
	pp:unit(pp:reset_color())
	let_helper(pp, name, debuginfo, expr, context)

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function unanchored_inferrable_term_override_pretty:let(pp, context)
	context = ensure_context(context)
	inferrable_let_or_tuple_elim(pp, self, context)
end

---@param pp PrettyPrint
---@param context AnyContext
function typed_term_override_pretty:let(pp, context)
	context = ensure_context(context)
	typed_let_or_tuple_elim(pp, self, context)
end

---@param pp PrettyPrint
---@param context AnyContext
function binding_override_pretty:tuple_elim(pp, context)
	local names, debuginfo, subject = self:unwrap_tuple_elim()
	context = ensure_context(context)

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit(enum_name(self, "tuple_elim "))
	pp:unit(pp:reset_color())
	tuple_elim_helper(pp, names, debuginfo, subject, context)

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function unanchored_inferrable_term_override_pretty:tuple_elim(pp, context)
	context = ensure_context(context)
	assert(not self:is_let())
	assert(self:is_tuple_elim())
	inferrable_let_or_tuple_elim(pp, self, context)
end

---@param pp PrettyPrint
---@param context AnyContext
function typed_term_override_pretty:tuple_elim(pp, context)
	context = ensure_context(context)
	typed_let_or_tuple_elim(pp, self, context)
end

---@param pp PrettyPrint
---@param context AnyContext
function binding_override_pretty:annotated_lambda(pp, context)
	local param_name, param_annotation, anchor, visible, pure = self:unwrap_annotated_lambda()
	context = ensure_context(context)

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit(enum_name(self, "λ🖉"))
	pp:_enter()
	pp:any(anchor, context)
	pp:_exit()
	pp:unit(pp:set_color())
	pp:unit("<")
	pp:any(visible, context)
	pp:unit(", ")
	pp:any(pure, context)
	pp:unit("> ")
	pp:unit(pp:reset_color())

	pp:any(param_name, context)

	pp:unit(pp:set_color())
	pp:unit(" : ")
	pp:unit(pp:reset_color())

	pp:any(param_annotation, context)

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function unanchored_inferrable_term_override_pretty:annotated_lambda(pp, context)
	local param_name, param_annotation, body, anchor, visible, pure = self:unwrap_annotated_lambda()
	context = ensure_context(context)
	local inner_context = context:append(param_name)
	local _, param_annotation = param_annotation:unwrap_anchored_inferrable()
	local is_tuple_type, desc = as_any_tuple_type(param_annotation)
	local is_destructure, is_rename, names, body, inner_context = inferrable_destructure_helper(body, inner_context)
	if is_rename then
		---@cast names string
		param_name = names
		is_destructure = false
	end

	local members
	if is_tuple_type then
		is_tuple_type, members = inferrable_tuple_type_flatten(desc, context)
	end

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit(enum_name(self, "λ🖉"))
	pp:_enter()
	pp:any(anchor, context)
	pp:_exit()
	pp:unit(pp:set_color())
	pp:unit("<")
	pp:any(visible, context)
	pp:unit(", ")
	pp:any(pure, context)
	pp:unit("> ")
	pp:unit(pp:reset_color())

	if is_tuple_type and is_destructure then
		---@cast names ArrayValue
		---@cast members TupleDescFlat[]
		if #members == 0 then
			pp:unit(pp:set_color())
			pp:unit("()")
			pp:unit(pp:reset_color())
		else
			tuple_type_helper(pp, members, names)
		end
	elseif is_destructure then
		---@cast names ArrayValue
		-- tuple_elim on param but its type isn't a tuple type???
		-- probably shouldn't happen, but here's a handler
		pp:unit(pp:set_color())
		pp:unit("(")
		pp:unit(pp:reset_color())

		for i, name in names:ipairs() do
			if i > 1 then
				pp:unit(" ")
			end
			pp:any(name, context)
		end

		pp:unit(pp:set_color())
		pp:unit(") : ")
		pp:unit(pp:reset_color())

		pp:any(param_annotation, context)
	else
		pp:any(param_name, context)

		pp:unit(pp:set_color())
		pp:unit(" : ")
		pp:unit(pp:reset_color())

		pp:any(param_annotation, context)
	end

	pp:unit(pp:set_color())
	pp:unit(" ->")
	pp:unit(pp:reset_color())

	if body:is_let() or body:is_tuple_elim() then
		pp:unit("\n")
		pp:_indent()
		pp:_prefix()
		pp:any(body, inner_context)
		pp:_dedent()
	else
		pp:unit(" ")
		pp:any(body, inner_context)
	end

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function typed_term_override_pretty:lambda(pp, context)
	local param_name, param_debug, body, capture, capture_debug, anchor = self:unwrap_lambda()
	context = ensure_context(context)
	local inner_context = context:append(param_name)
	local is_destructure, is_rename, names, body, inner_context = typed_destructure_helper(body, inner_context, capture)
	if is_rename then
		---@cast names string
		param_name = names
		is_destructure = false
	end

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit(enum_name(self, "λ🖉"))
	pp:_enter()
	pp:any(anchor, context)
	pp:_exit()
	pp:unit(pp:reset_color())
	pp:unit(" ")

	if is_destructure then
		pp:unit(pp:set_color())
		pp:unit("(")
		---@cast names ArrayValue
		for i, name in names:ipairs() do
			pp:unit(pp:reset_color())
			if i > 1 then
				pp:unit(" ")
			end
			pp:unit(name)
		end
		pp:unit(pp:set_color())
		pp:unit(")")
		pp:unit(pp:reset_color())
	else
		pp:unit(param_name)
	end

	pp:unit(pp:set_color())
	pp:unit(" ->")
	pp:unit(pp:reset_color())

	if body:is_let() or body:is_tuple_elim() then
		pp:unit("\n")
		pp:_indent()
		pp:_prefix()
		pp:any(body, inner_context)
		pp:_dedent()
	else
		pp:unit(" ")
		pp:any(body, inner_context)
	end

	pp:_exit()
end

---@param pp PrettyPrint
---@param ... any
function flex_value_override_pretty:strict(pp, ...)
	local strict = self:unwrap_strict()
	pp:unit(pp:set_color())
	pp:unit("flex.")
	pp:unit(pp:reset_color())
	pp:any(strict, ...)
end

---@param pp PrettyPrint
---@param ... any
function flex_value_override_pretty:stuck(pp, ...)
	local stuck = self:unwrap_stuck()
	pp:_enter()
	pp:unit(pp:set_color())
	pp:unit("flex.")
	pp:unit(pp:reset_color())
	pp:_exit()
	pp:any(stuck, ...)
end

---@param pp PrettyPrint
---@param context AnyContext
function flex_value_override_pretty:closure(pp, context)
	local param_name, code, capture, capture_debug, param_debug = self:unwrap_closure()
	local context = PrettyprintingContext.new()
	context = context:append(capture_debug.name)
	context = context:append(param_name)
	local is_destructure, is_rename, names, code, inner_context = typed_destructure_helper(code, context, capture)
	if is_rename then
		---@cast names string
		param_name = names
		is_destructure = false
	end

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit(enum_name(self, "closure "))
	pp:unit(pp:reset_color())

	if is_destructure then
		pp:unit(pp:set_color())
		pp:unit("(")
		---@cast names ArrayValue
		for i, name in names:ipairs() do
			pp:unit(pp:reset_color())
			if i > 1 then
				pp:unit(" ")
			end
			pp:unit(name)
		end
		pp:unit(pp:set_color())
		pp:unit(")")
		pp:unit(pp:reset_color())
	else
		pp:unit(param_name)
	end

	pp:unit(pp:set_color())
	pp:unit(" ->")
	pp:unit(pp:reset_color())

	if code:is_let() or code:is_tuple_elim() then
		pp:unit("\n")
		pp:_indent()
		pp:_prefix()
		pp:any(code, inner_context)
		pp:_dedent()
	else
		pp:unit(" ")
		pp:any(code, inner_context)
	end

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function unanchored_inferrable_term_override_pretty:pi(pp, context)
	-- extracting parameter names from the destructure of the result
	-- so that we get the name of the last parameter
	-- name of the last result is still lost
	local param_type, param_info, result_type, result_info = self:unwrap_pi()
	context = ensure_context(context)
	local result_context = context
	local _, param_type = param_type:unwrap_anchored_inferrable()
	local _, result_type = result_type:unwrap_anchored_inferrable()
	local param_is_tuple_type, param_desc = as_any_tuple_type(param_type)
	local result_is_readable, param_name, _, result_body, anchor = result_type:as_annotated_lambda()
	local result_is_destructure, result_is_rename, param_names, result_is_tuple_type, result_desc
	if result_is_readable then
		result_context = result_context:append(param_name)
		result_is_destructure, result_is_rename, param_names, result_body, result_context =
			inferrable_destructure_helper(result_body, result_context)
		if result_is_rename then
			---@cast param_names string
			param_name = param_names
			result_is_destructure = false
		end
		result_is_tuple_type, result_desc = as_any_tuple_type(result_body)
	end

	local param_members
	if param_is_tuple_type then
		param_is_tuple_type, param_members = inferrable_tuple_type_flatten(param_desc, context)
	end

	local result_members
	if result_is_readable and result_is_tuple_type then
		result_is_tuple_type, result_members = inferrable_tuple_type_flatten(result_desc, result_context)
	end

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit(enum_name(self, "Π🖉"))
	pp:_enter()
	pp:any(anchor, context)
	pp:_exit()
	pp:unit(pp:reset_color())
	pp:any(param_info, context)
	pp:unit(pp:set_color())
	pp:unit(", ")
	pp:unit(pp:reset_color())
	pp:any(result_info, context)
	pp:unit(pp:set_color())
	pp:unit("> ")
	pp:unit(pp:reset_color())

	if not result_is_readable then
		pp:any(param_type, context)
	elseif param_is_tuple_type and result_is_destructure then
		---@cast param_names ArrayValue
		---@cast param_members TupleDescFlat[]
		if #param_members == 0 then
			pp:unit(pp:set_color())
			pp:unit("()")
			pp:unit(pp:reset_color())
		else
			tuple_type_helper(pp, param_members, param_names)
		end
	elseif result_is_destructure then
		---@cast param_names ArrayValue
		-- tuple_elim on params but params aren't a tuple type???
		-- probably shouldn't happen, but here's a handler
		pp:unit(pp:set_color())
		pp:unit("(")
		pp:unit(pp:reset_color())

		for i, name in param_names:ipairs() do
			if i > 1 then
				pp:unit(" ")
			end
			pp:unit(name)
		end

		pp:unit(pp:set_color())
		pp:unit(") : ")
		pp:unit(pp:reset_color())

		pp:any(param_type, context)
	else
		pp:unit(param_name)

		pp:unit(pp:set_color())
		pp:unit(" : ")
		pp:unit(pp:reset_color())

		pp:any(param_type, context)
	end

	pp:unit(pp:set_color())
	pp:unit(" -> ")
	pp:unit(pp:reset_color())

	if not result_is_readable then
		pp:any(result_type, context)
	elseif result_is_tuple_type then
		---@cast result_members TupleDescFlat[]
		if #result_members == 0 then
			pp:unit(pp:set_color())
			pp:unit("()")
			pp:unit(pp:reset_color())
		else
			tuple_type_helper(pp, result_members)
		end
	else
		pp:any(result_body, result_context)
	end

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function unanchored_inferrable_term_override_pretty:host_function_type(pp, context)
	local param_type, result_type, result_info = self:unwrap_host_function_type()
	context = ensure_context(context)
	local result_context = context
	local _, param_type = param_type:unwrap_anchored_inferrable()
	local param_is_tuple_type, param_desc = param_type:as_host_tuple_type()
	local _, result_type = result_type:unwrap_anchored_inferrable()
	local result_is_readable, param_name, _, result_body, anchor = result_type:as_annotated_lambda()
	local result_is_destructure, result_is_rename, param_names, result_is_tuple_type, result_desc
	if result_is_readable then
		result_context = result_context:append(param_name)
		result_is_destructure, result_is_rename, param_names, result_body, result_context =
			inferrable_destructure_helper(result_body, result_context)
		if result_is_rename then
			---@cast param_names string
			param_name = param_names
			result_is_destructure = false
		end
		result_is_tuple_type, result_desc = result_body:as_host_tuple_type()
	end

	local param_members
	if param_is_tuple_type then
		param_is_tuple_type, param_members = inferrable_tuple_type_flatten(param_desc, context)
	end

	local result_members
	if result_is_readable and result_is_tuple_type then
		result_is_tuple_type, result_members = inferrable_tuple_type_flatten(result_desc, result_context)
	end

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit(enum_name(self, "host-Π🖉"))
	pp:_enter()
	pp:any(anchor, context)
	pp:_exit()
	pp:unit(pp:set_color())
	pp:unit("<")
	pp:unit(pp:reset_color())
	pp:any(result_info, context)
	pp:unit(pp:set_color())
	pp:unit("> ")
	pp:unit(pp:reset_color())

	if not result_is_readable then
		pp:any(param_type, context)
	elseif param_is_tuple_type and result_is_destructure then
		---@cast param_names ArrayValue
		---@cast param_members TupleDescFlat[]
		if #param_members == 0 then
			pp:unit(pp:set_color())
			pp:unit("()")
			pp:unit(pp:reset_color())
		else
			tuple_type_helper(pp, param_members, param_names)
		end
	elseif result_is_destructure then
		---@cast param_names ArrayValue
		-- tuple_elim on params but params aren't a tuple type???
		-- probably shouldn't happen, but here's a handler
		pp:unit(pp:set_color())
		pp:unit("(")
		pp:unit(pp:reset_color())

		for i, name in param_names:ipairs() do
			if i > 1 then
				pp:unit(" ")
			end
			pp:unit(name)
		end

		pp:unit(pp:set_color())
		pp:unit(") : ")
		pp:unit(pp:reset_color())

		pp:any(param_type, context)
	else
		pp:unit(param_name)

		pp:unit(pp:set_color())
		pp:unit(" : ")
		pp:unit(pp:reset_color())

		pp:any(param_type, context)
	end

	pp:unit(pp:set_color())
	pp:unit(" -> ")
	pp:unit(pp:reset_color())

	if not result_is_readable then
		pp:any(result_type, context)
	elseif result_is_tuple_type then
		---@cast result_members TupleDescFlat[]
		if #result_members == 0 then
			pp:unit(pp:set_color())
			pp:unit("()")
			pp:unit(pp:reset_color())
		else
			tuple_type_helper(pp, result_members)
		end
	else
		pp:any(result_body, result_context)
	end

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function typed_term_override_pretty:pi(pp, context)
	-- extracting parameter names from the destructure of the result
	-- so that we get the name of the last parameter
	-- name of the last result is still lost
	local param_type, param_info, result_type, result_info = self:unwrap_pi()
	context = ensure_context(context)
	local result_context = context
	local param_is_tuple_type, param_desc = as_any_tuple_type(param_type)
	local result_is_readable, param_name, param_debug, result_body, result_capture, result_capture_debug, result_start_anchor =
		result_type:as_lambda()
	local result_is_destructure, result_is_rename, param_names, result_is_tuple_type, result_desc
	if result_is_readable then
		result_context = result_context:append(param_name)
		result_is_destructure, result_is_rename, param_names, result_body, result_context =
			typed_destructure_helper(result_body, result_context, result_capture)
		if result_is_rename then
			---@cast param_names string
			param_name = param_names
			result_is_destructure = false
		end
		result_is_tuple_type, result_desc = as_any_tuple_type(result_body)
	end

	local param_members
	if param_is_tuple_type then
		param_is_tuple_type, param_members = typed_tuple_type_flatten(param_desc, context)
	end

	local result_members
	if result_is_readable and result_is_tuple_type then
		result_is_tuple_type, result_members = typed_tuple_type_flatten(result_desc, result_context)
	end

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit(enum_name(self, "Π <"))
	pp:unit(pp:reset_color())
	pp:any(param_info, context)
	pp:unit(pp:set_color())
	pp:unit(", ")
	pp:unit(pp:reset_color())
	pp:any(result_info, context)
	pp:unit(pp:set_color())
	pp:unit("> ")
	pp:unit(pp:reset_color())

	if not result_is_readable then
		pp:any(param_type, context)
	elseif param_is_tuple_type and result_is_destructure then
		---@cast param_names ArrayValue
		---@cast param_members TupleDescFlat[]
		if #param_members == 0 then
			pp:unit(pp:set_color())
			pp:unit("()")
			pp:unit(pp:reset_color())
		else
			tuple_type_helper(pp, param_members, param_names)
		end
	elseif result_is_destructure then
		---@cast param_names ArrayValue
		-- tuple_elim on params but params aren't a tuple type???
		-- probably shouldn't happen, but here's a handler
		pp:unit(pp:set_color())
		pp:unit("(")
		pp:unit(pp:reset_color())

		for i, name in param_names:ipairs() do
			if i > 1 then
				pp:unit(" ")
			end
			pp:unit(name)
		end

		pp:unit(pp:set_color())
		pp:unit(") : ")
		pp:unit(pp:reset_color())

		pp:any(param_type, context)
	else
		pp:unit(param_name)

		pp:unit(pp:set_color())
		pp:unit(" : ")
		pp:unit(pp:reset_color())

		pp:any(param_type, context)
	end

	pp:unit(pp:set_color())
	pp:unit(" -> ")
	pp:unit(pp:reset_color())

	if not result_is_readable then
		pp:any(result_type, context)
	elseif result_is_tuple_type then
		---@cast result_members TupleDescFlat[]
		if #result_members == 0 then
			pp:unit(pp:set_color())
			pp:unit("()")
			pp:unit(pp:reset_color())
		else
			tuple_type_helper(pp, result_members)
		end
	else
		pp:any(result_body, result_context)
	end

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function typed_term_override_pretty:host_function_type(pp, context)
	local param_type, result_type, result_info = self:unwrap_host_function_type()
	context = ensure_context(context)
	local result_context = context
	local param_is_tuple_type, param_desc = param_type:as_host_tuple_type()
	local result_is_readable, param_name, param_debug, result_body = result_type:as_lambda()
	local result_is_destructure, result_is_rename, param_names, result_is_tuple_type, result_desc
	if result_is_readable then
		result_context = result_context:append(param_name)
		result_is_destructure, result_is_rename, param_names, result_body, result_context =
			typed_destructure_helper(result_body, result_context)
		if result_is_rename then
			---@cast param_names string
			param_name = param_names
			result_is_destructure = false
		end
		result_is_tuple_type, result_desc = result_body:as_host_tuple_type()
	end

	local param_members
	if param_is_tuple_type then
		param_is_tuple_type, param_members = typed_tuple_type_flatten(param_desc, context)
	end

	local result_members
	if result_is_readable and result_is_tuple_type then
		result_is_tuple_type, result_members = typed_tuple_type_flatten(result_desc, result_context)
	end

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit(enum_name(self, "host-Π <"))
	pp:unit(pp:reset_color())
	pp:any(result_info, context)
	pp:unit(pp:set_color())
	pp:unit("> ")
	pp:unit(pp:reset_color())

	if not result_is_readable then
		pp:any(param_type, context)
	elseif param_is_tuple_type and result_is_destructure then
		---@cast param_names ArrayValue
		---@cast param_members TupleDescFlat[]
		if #param_members == 0 then
			pp:unit(pp:set_color())
			pp:unit("()")
			pp:unit(pp:reset_color())
		else
			tuple_type_helper(pp, param_members, param_names)
		end
	elseif result_is_destructure then
		---@cast param_names ArrayValue
		-- tuple_elim on params but params aren't a tuple type???
		-- probably shouldn't happen, but here's a handler
		pp:unit(pp:set_color())
		pp:unit("(")
		pp:unit(pp:reset_color())

		for i, name in param_names:ipairs() do
			if i > 1 then
				pp:unit(" ")
			end
			pp:unit(name)
		end

		pp:unit(pp:set_color())
		pp:unit(") : ")
		pp:unit(pp:reset_color())

		pp:any(param_type, context)
	else
		pp:unit(param_name)

		pp:unit(pp:set_color())
		pp:unit(" : ")
		pp:unit(pp:reset_color())

		pp:any(param_type, context)
	end

	pp:unit(pp:set_color())
	pp:unit(" -> ")
	pp:unit(pp:reset_color())

	if not result_is_readable then
		pp:any(result_type, context)
	elseif result_is_tuple_type then
		---@cast result_members TupleDescFlat[]
		if #result_members == 0 then
			pp:unit(pp:set_color())
			pp:unit("()")
			pp:unit(pp:reset_color())
		else
			tuple_type_helper(pp, result_members)
		end
	else
		pp:any(result_body, result_context)
	end

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function flex_value_override_pretty:pi(pp, context)
	local param_type, param_info, result_type, result_info = self:unwrap_pi()
	local param_is_tuple_type, param_desc = as_any_tuple_type(param_type)
	local result_is_readable, param_name, result_code, result_capture, result_capture_debug, param_debug =
		result_type:as_closure()
	local result_context, result_is_destructure, result_is_rename, param_names, result_is_tuple_type, result_desc
	if result_is_readable then
		result_context = PrettyprintingContext.new()
		result_context = result_context:append(result_capture_debug.name)
		result_context = result_context:append(param_name)
		result_is_destructure, result_is_rename, param_names, result_code, result_context =
			typed_destructure_helper(result_code, result_context, result_capture)
		if result_is_rename then
			---@cast param_names string
			param_name = param_names
			result_is_destructure = false
		end
		result_is_tuple_type, result_desc = as_any_tuple_type(result_code)
	end

	local param_members
	if param_is_tuple_type then
		param_is_tuple_type, param_members = value_tuple_type_flatten(param_desc)
	end

	local result_members
	if result_is_readable and result_is_tuple_type then
		result_is_tuple_type, result_members = typed_tuple_type_flatten(result_desc, result_context)
	end

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit(enum_name(self, "Π <"))
	pp:unit(pp:reset_color())
	pp:any(param_info, context)
	pp:unit(pp:set_color())
	pp:unit(", ")
	pp:unit(pp:reset_color())
	pp:any(result_info, context)
	pp:unit(pp:set_color())
	pp:unit("> ")
	pp:unit(pp:reset_color())

	if not result_is_readable then
		pp:any(param_type, context)
	elseif param_is_tuple_type and result_is_destructure then
		---@cast param_names ArrayValue
		---@cast param_members TupleDescFlat[]
		if #param_members == 0 then
			pp:unit(pp:set_color())
			pp:unit("()")
			pp:unit(pp:reset_color())
		else
			tuple_type_helper(pp, param_members, param_names)
		end
	elseif result_is_destructure then
		---@cast param_names ArrayValue
		-- tuple_elim on params but params aren't a tuple type???
		-- probably shouldn't happen, but here's a handler
		pp:unit(pp:set_color())
		pp:unit("(")
		pp:unit(pp:reset_color())

		for i, name in param_names:ipairs() do
			if i > 1 then
				pp:unit(" ")
			end
			pp:any(name, context)
		end

		pp:unit(pp:set_color())
		pp:unit(") : ")
		pp:unit(pp:reset_color())

		pp:any(param_type, context)
	else
		pp:any(param_name, context)

		pp:unit(pp:set_color())
		pp:unit(" : ")
		pp:unit(pp:reset_color())

		pp:any(param_type, context)
	end

	pp:unit(pp:set_color())
	pp:unit(" -> ")
	pp:unit(pp:reset_color())

	if not result_is_readable then
		pp:any(result_type, context)
	elseif result_is_tuple_type then
		---@cast result_members TupleDescFlat[]
		if #result_members == 0 then
			pp:unit(pp:set_color())
			pp:unit("()")
			pp:unit(pp:reset_color())
		else
			tuple_type_helper(pp, result_members)
		end
	else
		pp:any(result_code, result_context)
	end

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function flex_value_override_pretty:host_function_type(pp, context)
	local param_type, result_type, result_info = self:unwrap_host_function_type()
	local param_is_tuple_type, param_desc = param_type:as_host_tuple_type()
	local result_is_readable, param_name, result_code, result_capture, result_capture_debug, param_debug =
		result_type:as_closure()
	local result_context, result_is_destructure, result_is_rename, param_names, result_is_tuple_type, result_desc
	if result_is_readable then
		result_context = PrettyprintingContext.new()
		result_context = result_context:append(result_capture_debug.name)
		result_context = result_context:append(param_name)
		result_is_destructure, result_is_rename, param_names, result_code, result_context =
			typed_destructure_helper(result_code, result_context, result_capture)
		if result_is_rename then
			---@cast param_names string
			param_name = param_names
			result_is_destructure = false
		end
		result_is_tuple_type, result_desc = result_code:as_host_tuple_type()
	end

	local param_members
	if param_is_tuple_type then
		param_is_tuple_type, param_members = value_tuple_type_flatten(param_desc)
	end

	local result_members
	if result_is_readable and result_is_tuple_type then
		result_is_tuple_type, result_members = typed_tuple_type_flatten(result_desc, result_context)
	end

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit(enum_name(self, "host-Π <"))
	pp:unit(pp:reset_color())
	pp:any(result_info, context)
	pp:unit(pp:set_color())
	pp:unit("> ")
	pp:unit(pp:reset_color())

	if not result_is_readable then
		pp:any(param_type, context)
	elseif param_is_tuple_type and result_is_destructure then
		---@cast param_names ArrayValue
		---@cast param_members TupleDescFlat[]
		if #param_members == 0 then
			pp:unit(pp:set_color())
			pp:unit("()")
			pp:unit(pp:reset_color())
		else
			tuple_type_helper(pp, param_members, param_names)
		end
	elseif result_is_destructure then
		---@cast param_names ArrayValue
		-- tuple_elim on params but params aren't a tuple type???
		-- probably shouldn't happen, but here's a handler
		pp:unit(pp:set_color())
		pp:unit("(")
		pp:unit(pp:reset_color())

		for i, name in param_names:ipairs() do
			if i > 1 then
				pp:unit(" ")
			end
			pp:any(name, context)
		end

		pp:unit(pp:set_color())
		pp:unit(") : ")
		pp:unit(pp:reset_color())

		pp:any(param_type, context)
	else
		pp:any(param_name, context)

		pp:unit(pp:set_color())
		pp:unit(" : ")
		pp:unit(pp:reset_color())

		pp:any(param_type, context)
	end

	pp:unit(pp:set_color())
	pp:unit(" -> ")
	pp:unit(pp:reset_color())

	if not result_is_readable then
		pp:any(result_type, context)
	elseif result_is_tuple_type then
		---@cast result_members TupleDescFlat[]
		if #result_members == 0 then
			pp:unit(pp:set_color())
			pp:unit("()")
			pp:unit(pp:reset_color())
		else
			tuple_type_helper(pp, result_members)
		end
	else
		pp:any(result_code, result_context)
	end

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function flex_value_override_pretty:visibility(pp, context)
	local v = self:unwrap_visibility()

	pp:_enter()

	pp:unit(pp:set_color())
	if v:is_implicit() then
		pp:unit("implicit")
	elseif v:is_explicit() then
		pp:unit("explicit")
	else
		pp:any(v, context)
	end
	pp:unit(pp:reset_color())

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function flex_value_override_pretty:param_info(pp, context)
	local v = self:unwrap_param_info()
	pp:any(v, context)
end

---@param pp PrettyPrint
---@param context AnyContext
function flex_value_override_pretty:result_info(pp, context)
	local purity = self:unwrap_result_info():unwrap_result_info()
	pp:any(purity, context)
end

---@param pp PrettyPrint
---@param context AnyContext
function unanchored_inferrable_term_override_pretty:application(pp, context)
	local f, arg = self:unwrap_application()
	context = ensure_context(context)

	-- handle nested applications
	---@param f anchored_inferrable
	---@param arg checkable
	local function application_inner(f, arg)
		local _, f = f:unwrap_anchored_inferrable()
		local f_is_application, f_f, f_arg = f:as_application()
		local f_is_typed, _, _, f_typed_term = f:as_typed()
		local f_is_bound_variable, f_index = false, 0
		if f_is_typed then
			f_is_bound_variable, f_index, _ = f_typed_term:as_bound_variable()
		end

		pp:_enter()

		-- print pretty on certain conditions, or fall back to apply()
		if
			(f_is_application or (f_is_typed and f_is_bound_variable and context:len() >= f_index))
			and (arg:is_tuple_cons() or arg:is_host_tuple_cons())
		then
			if f_is_application then
				application_inner(f_f, f_arg)
			else
				pp:any(context:get_name(f_index), context)
			end

			local ok, elements, _ = arg:as_tuple_cons()
			elements = ok and elements or arg:unwrap_host_tuple_cons()

			pp:unit(pp:set_color())
			pp:unit("(")
			pp:unit(pp:reset_color())

			for i, arg in elements:ipairs() do
				if i > 1 then
					pp:unit(pp:set_color())
					pp:unit(", ")
					pp:unit(pp:reset_color())
				end

				pp:any(arg, context)
			end

			pp:unit(pp:set_color())
			pp:unit(")")
			pp:unit(pp:reset_color())
		else
			-- if we're here then the args are probably horrible
			-- add some newlines
			pp:unit(pp:set_color())
			pp:unit(enum_name(f, "apply("))
			pp:unit(pp:reset_color())
			pp:unit("\n")

			pp:_indent()

			pp:_prefix()
			pp:any(f, context)
			pp:unit(pp:set_color())
			pp:unit(",")
			pp:unit(pp:reset_color())
			pp:unit("\n")

			pp:_prefix()
			pp:any(arg, context)
			pp:unit("\n")

			pp:_dedent()

			pp:_prefix()
			pp:unit(pp:set_color())
			pp:unit(")")
			pp:unit(pp:reset_color())
		end

		pp:_exit()
	end

	application_inner(f, arg)
end

---@param pp PrettyPrint
---@param context AnyContext
function typed_term_override_pretty:application(pp, context)
	local f, arg = self:unwrap_application()
	context = ensure_context(context)

	--- handle nested applications
	---@param f typed
	---@param arg typed
	local function application_inner(f, arg)
		local f_is_application, f_f, f_arg = f:as_application()
		local f_is_bound_variable, f_index, _ = f:as_bound_variable()

		pp:_enter()

		-- print pretty on certain conditions, or fall back to apply()
		if
			(f_is_application or (f_is_bound_variable and context:len() >= f_index))
			and (arg:is_tuple_cons() or arg:is_host_tuple_cons())
		then
			if f_is_application then
				application_inner(f_f, f_arg)
			else
				pp:any(context:get_name(f_index), context)
			end

			local ok, elements = arg:as_tuple_cons()
			elements = ok and elements or arg:unwrap_host_tuple_cons()

			pp:unit(pp:set_color())
			pp:unit("(")
			pp:unit(pp:reset_color())

			for i, arg in elements:ipairs() do
				if i > 1 then
					pp:unit(pp:set_color())
					pp:unit(", ")
					pp:unit(pp:reset_color())
				end

				pp:any(arg, context)
			end

			pp:unit(pp:set_color())
			pp:unit(")")
			pp:unit(pp:reset_color())
		else
			-- if we're here then the args are probably horrible
			-- add some newlines
			pp:unit(pp:set_color())
			pp:unit(enum_name(f, "apply("))
			pp:unit(pp:reset_color())
			pp:unit("\n")

			pp:_indent()

			pp:_prefix()
			pp:any(f, context)
			pp:unit(pp:set_color())
			pp:unit(",")
			pp:unit(pp:reset_color())
			pp:unit("\n")

			pp:_prefix()
			pp:any(arg, context)
			pp:unit("\n")

			pp:_dedent()

			pp:_prefix()
			pp:unit(pp:set_color())
			pp:unit(")")
			pp:unit(pp:reset_color())
		end

		pp:_exit()
	end

	application_inner(f, arg)
end

---@param pp PrettyPrint
---@param context AnyContext
function unanchored_inferrable_term_override_pretty:tuple_type(pp, context)
	local desc = self:unwrap_tuple_type()
	context = ensure_context(context)
	local ok, members = inferrable_tuple_type_flatten(desc, context)

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit(enum_name(self, "tuple_type["))
	pp:unit(pp:reset_color())

	if ok then
		---@cast members TupleDescFlat[]
		tuple_type_helper(pp, members)
	else
		pp:any(desc, context)
	end

	pp:unit(pp:set_color())
	pp:unit("]")
	pp:unit(pp:reset_color())

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function unanchored_inferrable_term_override_pretty:host_tuple_type(pp, context)
	local desc = self:unwrap_host_tuple_type()
	context = ensure_context(context)
	local ok, members = inferrable_tuple_type_flatten(desc, context)

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit(enum_name(self, "host_tuple_type["))
	pp:unit(pp:reset_color())

	if ok then
		---@cast members TupleDescFlat[]
		tuple_type_helper(pp, members)
	else
		pp:any(desc, context)
	end

	pp:unit(pp:set_color())
	pp:unit("]")
	pp:unit(pp:reset_color())

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function typed_term_override_pretty:tuple_type(pp, context)
	local desc = self:unwrap_tuple_type()
	context = ensure_context(context)
	local ok, members = typed_tuple_type_flatten(desc, context)

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit(enum_name(self, "tuple_type["))
	pp:unit(pp:reset_color())

	if ok then
		---@cast members TupleDescFlat[]
		tuple_type_helper(pp, members)
	else
		pp:any(desc, context)
	end

	pp:unit(pp:set_color())
	pp:unit("]")
	pp:unit(pp:reset_color())

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function typed_term_override_pretty:host_tuple_type(pp, context)
	local desc = self:unwrap_host_tuple_type()
	context = ensure_context(context)
	local ok, members = typed_tuple_type_flatten(desc, context)

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit(enum_name(self, "host_tuple_type["))
	pp:unit(pp:reset_color())

	if ok then
		---@cast members TupleDescFlat[]
		tuple_type_helper(pp, members)
	else
		pp:any(desc, context)
	end

	pp:unit(pp:set_color())
	pp:unit("]")
	pp:unit(pp:reset_color())

	pp:_exit()
end

---@param pp PrettyPrint
function flex_value_override_pretty:tuple_type(pp)
	local desc = self:unwrap_tuple_type()
	local ok, members = value_tuple_type_flatten(desc)

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit(enum_name(self, "tuple_type["))
	pp:unit(pp:reset_color())

	if ok then
		---@cast members TupleDescFlat[]
		tuple_type_helper(pp, members)
	else
		pp:any(desc, context)
	end

	pp:unit(pp:set_color())
	pp:unit("]")
	pp:unit(pp:reset_color())

	pp:_exit()
end

---@param pp PrettyPrint
function flex_value_override_pretty:host_tuple_type(pp)
	local desc = self:unwrap_host_tuple_type()
	local ok, members = value_tuple_type_flatten(desc)

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit(enum_name(self, "host_tuple_type["))
	pp:unit(pp:reset_color())

	if ok then
		---@cast members TupleDescFlat[]
		tuple_type_helper(pp, members)
	else
		pp:any(desc, context)
	end

	pp:unit(pp:set_color())
	pp:unit("]")
	pp:unit(pp:reset_color())

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function flex_value_override_pretty:enum_value(pp, context)
	local constructor, arg = self:unwrap_enum_value()

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit(enum_name(self, "◬"))
	pp:unit(constructor)

	if arg:is_tuple_value() then
		local elements = arg:unwrap_tuple_value()

		pp:unit("(")
		pp:unit(pp:reset_color())

		for i, arg in elements:ipairs() do
			if i > 1 then
				pp:unit(pp:set_color())
				pp:unit(", ")
				pp:unit(pp:reset_color())
			end

			pp:any(arg, context)
		end

		pp:unit(pp:set_color())
		pp:unit(")")
		pp:unit(pp:reset_color())
	else
		pp:unit("[")
		pp:unit(pp:reset_color())

		pp:any(arg, context)

		pp:unit(pp:set_color())
		pp:unit("]")
		pp:unit(pp:reset_color())
	end

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function flex_value_override_pretty:free(pp, context)
	local free = self:unwrap_free()

	if free:is_metavariable() then
		local mv = free:unwrap_metavariable()

		pp:_enter()

		pp:unit(pp:set_color())
		pp:unit("⩤ ")
		pp:unit(tostring(mv.value))
		pp:unit(":")
		pp:unit(tostring(mv.usage))
		pp:unit("|")
		pp:unit(tostring(mv.block_level))
		pp:unit(" ⩥")
		pp:unit(tostring(pp:reset_color()))

		pp:_exit()
	else
		pp:record(enum_name(self, "free"), { { "free", free } }, context)
	end
end

---@param pp PrettyPrint
---@param context AnyContext
function typed_term_override_pretty:tuple_element_access(pp, context)
	local subject, index = self:unwrap_tuple_element_access()
	context = ensure_context(context)
	local subject_is_bound_variable, subject_index, subject_debug = subject:as_bound_variable()

	if subject_is_bound_variable and context:len() >= subject_index then
		pp:_enter()

		-- pp:unit(pp:set_color())
		-- pp:unit(enum_name(self, "tuple_element_access→"))
		-- pp:unit(pp:reset_color())

		local name = context:get_name(subject_index)
		pp:any(name, context)

		pp:unit(pp:set_color())
		pp:unit(".")
		pp:unit(pp:reset_color())

		pp:unit(tostring(index))

		local debug_name, debug_anchor = subject_debug:unwrap_var_debug()
		if debug_name == name then
			pp:unit(pp:set_color())
			pp:unit("🖉")

			pp:_enter()
			pp:any(debug_anchor, context)
			pp:_exit()
			pp:unit(pp:reset_color())
		else
			pp:unit(pp:set_color())
			pp:unit("<")
			pp:unit(pp:reset_color())

			pp:_enter()
			pp:any(subject_debug, context)
			pp:_exit()

			pp:unit(pp:set_color())
			pp:unit(">")
			pp:unit(pp:reset_color())
		end

		pp:_exit()
	else
		pp:set_color()
		pp:record(enum_name(self, "tuple_element_access"), { { "subject", subject }, { "index", index } }, context)
	end
end

---@param pp PrettyPrint
---@param context AnyContext
function typed_term_override_pretty:host_intrinsic(pp, context)
	local source, _ = self:unwrap_host_intrinsic()

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit(enum_name(self, "host_intrinsic "))
	pp:unit(pp:reset_color())

	local source_text
	local ok, source_val = source:as_literal()
	if ok then
		ok, source_text = source_val:as_host_value()
	end
	if ok and type(source_text) == "string" then
		-- trim initial newlines
		-- get first line
		-- ellipsize further lines
		local source_print = string.gsub(source_text, "^%c*(%C*)(.*)", function(visible, rest)
			if #rest > 0 then
				return visible .. " ..."
			else
				return visible
			end
		end)

		pp:unit(source_print)
	else
		pp:any(source, context)
	end

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function typed_term_override_pretty:constrained_type(pp, context)
	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit(enum_name(self, "constrained_type"))
	pp:unit(pp:reset_color())

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function flex_value_override_pretty:star(pp, context)
	local level, depth = self:unwrap_star()

	pp:_enter()

	pp:unit(pp:set_color())
	pp:unit("✪ ")
	pp:any(level, context)
	pp:unit("|")
	pp:any(depth, context)
	pp:unit(pp:reset_color())

	pp:_exit()
end

return function(args)
	typechecking_context_type = args.typechecking_context_type
	strict_runtime_context_type = args.strict_runtime_context_type
	flex_runtime_context_type = args.flex_runtime_context_type
	DescCons = args.DescCons
	return {
		checkable_term_override_pretty = checkable_term_override_pretty,
		unanchored_inferrable_term_override_pretty = unanchored_inferrable_term_override_pretty,
		typed_term_override_pretty = typed_term_override_pretty,
		flex_value_override_pretty = flex_value_override_pretty,
		stuck_value_override_pretty = stuck_value_override_pretty,
		binding_override_pretty = binding_override_pretty,
		var_debug_override_pretty = var_debug_override_pretty,
	}
end
