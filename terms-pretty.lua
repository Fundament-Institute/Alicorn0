local fibbuf = require "fibonacci-buffer"
local gen = require "terms-generators"
local typechecking_context_type
local runtime_context_type
local DescCons

-- pretty printing context stuff

local prettyprinting_context_mt = {}

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
	local self = {}
	self.bindings = context.bindings
	return setmetatable(self, prettyprinting_context_mt)
end

---@param context RuntimeContext
---@return PrettyPrintingContext
function PrettyprintingContext.from_runtime_context(context)
	local self = {}
	self.bindings = context.bindings
	return setmetatable(self, prettyprinting_context_mt)
end

---@param index integer
---@return string
function PrettyprintingContext:get_name(index)
	return self.bindings:get(index).name
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

local prettyprinting_context_type =
	gen.declare_foreign(gen.metatable_equality(prettyprinting_context_mt), "PrettyPrintingContext")

---@alias AnyContext PrettyPrintingContext | TypecheckingContext | RuntimeContext

---@param context AnyContext
---@return PrettyPrintingContext
local function ensure_context(context)
	if prettyprinting_context_type.value_check(context) == true then
		---@cast context PrettyPrintingContext
		return context
	elseif typechecking_context_type.value_check(context) == true then
		---@cast context TypecheckingContext
		return PrettyprintingContext.from_typechecking_context(context)
	elseif runtime_context_type.value_check(context) == true then
		---@cast context RuntimeContext
		return PrettyprintingContext.from_runtime_context(context)
	else
		--print("!!!!!!!!!! MISSING PRETTYPRINTER CONTEXT !!!!!!!!!!!!!!")
		--print("making something up")
		return PrettyprintingContext.new():append("#made-up")
	end
end

-- generic helper functions

---@param pp PrettyPrint
---@param name string
---@param expr inferrable | typed
---@param context PrettyPrintingContext
---@return PrettyPrintingContext
local function let_helper(pp, name, expr, context)
	pp:unit(name)

	pp:unit(pp:_color())
	pp:unit(" = ")
	pp:unit(pp:_resetcolor())

	pp:_indent()
	pp:any(expr, context)
	pp:_dedent()

	context = context:append(name)

	return context
end

---@param pp PrettyPrint
---@param names ArrayValue
---@param subject inferrable | typed
---@param context PrettyPrintingContext
---@return PrettyPrintingContext
local function tuple_elim_helper(pp, names, subject, context)
	local inner_context = context

	pp:unit(pp:_color())
	pp:unit("(")
	pp:unit(pp:_resetcolor())

	for i, name in names:ipairs() do
		inner_context = inner_context:append(name)

		if i > 1 then
			pp:unit(pp:_color())
			pp:unit(", ")
			pp:unit(pp:_resetcolor())
		end

		pp:unit(name)
	end

	pp:unit(pp:_color())
	pp:unit(") = ")
	pp:unit(pp:_resetcolor())

	pp:any(subject, context)

	return inner_context
end

---@class (exact) TupleDescFlat
---@field [1] ArrayValue
---@field [2] inferrable | typed
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

		pp:unit(pp:_color())
		pp:unit("(")
		pp:unit(pp:_resetcolor())

		if i > n then
			pp:unit(string.format("#unk%d", i))
		else
			pp:unit(names[i])
		end

		pp:unit(pp:_color())
		pp:unit(" : ")
		pp:unit(pp:_resetcolor())

		pp:any(mem[2], mem[3])

		pp:unit(pp:_color())
		pp:unit(")")
		pp:unit(pp:_resetcolor())
	end
end

---@generic T
---@param term T
---@return boolean
---@return T?
local function as_any_tuple_type(term)
	---@cast term inferrable|value|typed
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
---@param term inferrable
---@param context PrettyPrintingContext
local function inferrable_let_or_tuple_elim(pp, term, context)
	pp:_enter()

	local name, expr, names, subject
	while true do
		if term:is_let() then
			name, expr, term = term:unwrap_let()

			-- rear-loading prefix to cheaply handle first loop not needing prefix
			pp:unit(pp:_color())
			pp:unit("inferrable.let ")
			pp:unit(pp:_resetcolor())
			context = let_helper(pp, name, expr, context)
			pp:unit("\n")
			pp:_prefix()
		elseif term:is_tuple_elim() then
			names, subject, term = term:unwrap_tuple_elim()

			pp:unit(pp:_color())
			pp:unit("inferrable.let ")
			pp:unit(pp:_resetcolor())
			context = tuple_elim_helper(pp, names, subject, context)
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
			name, expr, term = term:unwrap_let()

			-- rear-loading prefix to cheaply handle first loop not needing prefix
			pp:unit(pp:_color())
			pp:unit("typed.let ")
			pp:unit(pp:_resetcolor())
			context = let_helper(pp, name, expr, context)
			pp:unit("\n")
			pp:_prefix()
		elseif term:is_tuple_elim() then
			names, subject, _, term = term:unwrap_tuple_elim()

			pp:unit(pp:_color())
			pp:unit("typed.let ")
			pp:unit(pp:_resetcolor())
			context = tuple_elim_helper(pp, names, subject, context)
			pp:unit("\n")
			pp:_prefix()
		else
			break
		end
	end

	pp:any(term, context)

	pp:_exit()
end

---@param term inferrable
---@param context PrettyPrintingContext
---@return boolean
---@return boolean
---@return (string | ArrayValue)?
---@return inferrable
---@return PrettyPrintingContext
local function inferrable_destructure_helper(term, context)
	if term:is_let() then
		-- destructuring with a let effectively just renames the parameter
		-- thus it's usually superfluous to write code like this
		-- and probably unwise to elide the let
		-- but some operatives that are generic over lets and tuple-elims do this
		-- e.g. forall, lambda
		-- so we pretty this anyway
		local name, expr, body = term:unwrap_let()
		local ok, index = expr:as_bound_variable()
		local is_destructure = ok and index == context:len()
		if is_destructure then
			context = context:append(name)
			return true, true, name, body, context
		end
	elseif term:is_tuple_elim() then
		local names, subject, body = term:unwrap_tuple_elim()
		local ok, index = subject:as_bound_variable()
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
---@return boolean
---@return boolean
---@return (string | ArrayValue)?
---@return typed
---@return PrettyPrintingContext
local function typed_destructure_helper(term, context)
	if term:is_let() then
		-- destructuring with a let effectively just renames the parameter
		-- thus it's usually superfluous to write code like this
		-- and probably unwise to elide the let
		-- but some operatives that are generic over lets and tuple-elims do this
		-- e.g. forall, lambda
		-- so we pretty this anyway
		local name, expr, body = term:unwrap_let()
		local ok, index = expr:as_bound_variable()
		local is_destructure = ok and index == context:len()
		if is_destructure then
			context = context:append(name)
			return is_destructure, true, name, body, context
		end
	elseif term:is_tuple_elim() then
		local names, subject, _, body = term:unwrap_tuple_elim()
		local ok, index = subject:as_bound_variable()
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

---@param desc inferrable
---@param context PrettyPrintingContext
---@return boolean
---@return TupleDescFlat[]?
---@return integer?
local function inferrable_tuple_type_flatten(desc, context)
	local ok, constructor, arg = desc:as_enum_cons()
	if not ok then
		return false
	end
	if constructor == DescCons.empty then
		return true, {}, 0
	elseif constructor == DescCons.cons then
		local elements = arg:unwrap_tuple_cons()
		if elements:len() ~= 2 then
			return false
		end
		local desc = elements[1]
		local f = elements[2]
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

-- flatten at all costs!!
---@param desc inferrable
---@return (inferrable|string)[]
---@return integer
local function inferrable_tuple_type_hydraulicpress(desc)
	local ok, constructor, arg = desc:as_enum_cons()
	if not ok then
		return { "<UNHANDLED EDGE CASE>" }, 1
	end
	if constructor == DescCons.empty then
		return {}, 0
	elseif constructor == DescCons.cons then
		local elements = arg:unwrap_tuple_cons()
		if elements:len() ~= 2 then
			return { "<UNHANDLED EDGE CASE>" }, 1
		end
		local desc = elements[1]
		local f = elements[2]
		local prev, n = inferrable_tuple_type_hydraulicpress(desc)
		n = n + 1
		prev[n] = f
		return prev, n
	else
		return { "<UNHANDLED EDGE CASE>" }, 1
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
		local elements = arg:unwrap_tuple_cons()
		if elements:len() ~= 2 then
			return false
		end
		local desc = elements[1]
		local f = elements[2]
		local ok, param_name, body = f:as_lambda()
		if not ok then
			return false
		end
		local inner_context = context:append(param_name)
		local _, _, names, body, inner_context = typed_destructure_helper(body, inner_context)
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

-- flatten at all costs!!
---@param desc typed
---@return (typed|string)[]
---@return integer
local function typed_tuple_type_hydraulicpress(desc)
	local ok, constructor, arg = desc:as_enum_cons()
	if not ok then
		return { "<UNHANDLED EDGE CASE>" }, 1
	end
	if constructor == DescCons.empty then
		return {}, 0
	elseif constructor == DescCons.cons then
		local elements = arg:unwrap_tuple_cons()
		if elements:len() ~= 2 then
			return { "<UNHANDLED EDGE CASE>" }, 1
		end
		local desc = elements[1]
		local f = elements[2]
		local prev, n = typed_tuple_type_hydraulicpress(desc)
		n = n + 1
		prev[n] = f
		return prev, n
	else
		return { "<UNHANDLED EDGE CASE>" }, 1
	end
end

---@param desc value
---@return boolean
---@return TupleDescFlat[]?
---@return integer?
local function value_tuple_type_flatten(desc)
	local constructor, arg = desc:unwrap_enum_value()
	if constructor == DescCons.empty then
		return true, {}, 0
	elseif constructor == DescCons.cons then
		local elements = arg:unwrap_tuple_value()
		if elements:len() ~= 2 then
			return false
		end
		local desc = elements[1]
		local f = elements[2]
		local ok, param_name, code, capture = f:as_closure()
		if not ok then
			return false
		end
		local context = ensure_context(capture)
		local inner_context = context:append(param_name)
		local _, _, names, code, inner_context = typed_destructure_helper(code, inner_context)
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

-- flatten at all costs!!
---@param desc value
---@return (value|string)[]
---@return integer
local function value_tuple_type_hydraulicpress(desc)
	local constructor, arg = desc:unwrap_enum_value()
	if constructor == DescCons.empty then
		return {}, 0
	elseif constructor == DescCons.cons then
		local elements = arg:unwrap_tuple_value()
		if elements:len() ~= 2 then
			return { "<UNHANDLED EDGE CASE>" }, 1
		end
		local desc = elements[1]
		local f = elements[2]
		local prev, n = value_tuple_type_hydraulicpress(desc)
		n = n + 1
		prev[n] = f
		return prev, n
	else
		return { "<UNHANDLED EDGE CASE>" }, 1
	end
end

-- pretty printing impls
-- helplessly copypasted in unhealthy quantities
-- maintainers beware

---@class BindingOverridePretty : binding
local binding_override_pretty = {}

---@class CheckableTermOverride : checkable
local checkable_term_override_pretty = {}

---@class InferrableTermOverride : inferrable
local inferrable_term_override_pretty = {}

---@class TypedTermOverride : typed
local typed_term_override_pretty = {}

---@class ValueOverridePretty : value
local value_override_pretty = {}

---@param pp PrettyPrint
---@param context AnyContext
function checkable_term_override_pretty:inferrable(pp, context)
	local inferrable_term = self:unwrap_inferrable()
	context = ensure_context(context)
	pp:any(inferrable_term, context)
end

---@param pp PrettyPrint
---@param context AnyContext
function inferrable_term_override_pretty:typed(pp, context)
	local type, _, typed_term = self:unwrap_typed()
	context = ensure_context(context)

	pp:_enter()

	pp:unit(pp:_color())
	pp:unit("inferrable.the (")
	pp:unit(pp:_resetcolor())

	pp:any(type)

	pp:unit(pp:_color())
	pp:unit(") (")
	pp:unit(pp:_resetcolor())

	pp:any(typed_term, context)

	pp:unit(pp:_color())
	pp:unit(")")
	pp:unit(pp:_resetcolor())

	pp:_exit()
end

---@param pp PrettyPrint
function typed_term_override_pretty:literal(pp)
	local literal_value = self:unwrap_literal()
	pp:any(literal_value)
end

---@param pp PrettyPrint
---@param context AnyContext
function inferrable_term_override_pretty:bound_variable(pp, context)
	local index = self:unwrap_bound_variable()
	context = ensure_context(context)

	pp:_enter()

	if context:len() >= index then
		pp:unit(context:get_name(index))
	else
		-- TODO: warn on context too short?
		pp:unit(pp:_color())
		pp:unit("inferrable.bound_variable(")
		pp:unit(pp:_resetcolor())

		pp:unit(tostring(index))

		pp:unit(pp:_color())
		pp:unit(")")
		pp:unit(pp:_resetcolor())
	end

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function typed_term_override_pretty:bound_variable(pp, context)
	local index = self:unwrap_bound_variable()
	context = ensure_context(context)

	pp:_enter()

	if context:len() >= index then
		pp:unit(context:get_name(index))
	else
		-- TODO: warn on context too short?
		pp:unit(pp:_color())
		pp:unit("typed.bound_variable(")
		pp:unit(pp:_resetcolor())

		pp:unit(tostring(index))

		pp:unit(pp:_color())
		pp:unit(")")
		pp:unit(pp:_resetcolor())
	end

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function binding_override_pretty:let(pp, context)
	local name, expr = self:unwrap_let()
	context = ensure_context(context)

	pp:_enter()

	pp:unit(pp:_color())
	pp:unit("binding.let ")
	pp:unit(pp:_resetcolor())
	let_helper(pp, name, expr, context)

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function inferrable_term_override_pretty:let(pp, context)
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
	local names, subject = self:unwrap_tuple_elim()
	context = ensure_context(context)

	pp:_enter()

	pp:unit(pp:_color())
	pp:unit("binding.let ")
	pp:unit(pp:_resetcolor())
	tuple_elim_helper(pp, names, subject, context)

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function inferrable_term_override_pretty:tuple_elim(pp, context)
	context = ensure_context(context)
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
	local param_name, param_annotation, _, _ = self:unwrap_annotated_lambda()
	context = ensure_context(context)

	pp:_enter()

	pp:unit(pp:_color())
	pp:unit("binding.\u{03BB} ")
	pp:unit(pp:_resetcolor())

	pp:unit(param_name)

	pp:unit(pp:_color())
	pp:unit(" : ")
	pp:unit(pp:_resetcolor())

	pp:any(param_annotation, context)

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function inferrable_term_override_pretty:annotated_lambda(pp, context)
	local param_name, param_annotation, body, _, _ = self:unwrap_annotated_lambda()
	context = ensure_context(context)
	local inner_context = context:append(param_name)
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

	pp:unit(pp:_color())
	pp:unit("inferrable.\u{03BB} ")
	pp:unit(pp:_resetcolor())

	if is_tuple_type and is_destructure then
		---@cast names ArrayValue
		---@cast members TupleDescFlat[]
		if #members == 0 then
			pp:unit(pp:_color())
			pp:unit("()")
			pp:unit(pp:_resetcolor())
		else
			tuple_type_helper(pp, members, names)
		end
	elseif is_destructure then
		---@cast names ArrayValue
		-- tuple_elim on param but its type isn't a tuple type???
		-- probably shouldn't happen, but here's a handler
		pp:unit(pp:_color())
		pp:unit("(")
		pp:unit(pp:_resetcolor())

		for i, name in names:ipairs() do
			if i > 1 then
				pp:unit(" ")
			end
			pp:unit(name)
		end

		pp:unit(pp:_color())
		pp:unit(") : ")
		pp:unit(pp:_resetcolor())

		pp:any(param_annotation, context)
	else
		pp:unit(param_name)

		pp:unit(pp:_color())
		pp:unit(" : ")
		pp:unit(pp:_resetcolor())

		pp:any(param_annotation, context)
	end

	pp:unit(pp:_color())
	pp:unit(" ->")
	pp:unit(pp:_resetcolor())

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
	local param_name, body = self:unwrap_lambda()
	context = ensure_context(context)
	local inner_context = context:append(param_name)
	local is_destructure, is_rename, names, body, inner_context = typed_destructure_helper(body, inner_context)
	if is_rename then
		---@cast names string
		param_name = names
		is_destructure = false
	end

	pp:_enter()

	pp:unit(pp:_color())
	pp:unit("typed.\u{03BB} ")
	pp:unit(pp:_resetcolor())

	if is_destructure then
		---@cast names ArrayValue
		if names:len() == 0 then
			pp:unit(pp:_color())
			pp:unit("()")
			pp:unit(pp:_resetcolor())
		end

		for i, name in names:ipairs() do
			if i > 1 then
				pp:unit(" ")
			end
			pp:unit(name)
		end
	else
		pp:unit(param_name)
	end

	pp:unit(pp:_color())
	pp:unit(" ->")
	pp:unit(pp:_resetcolor())

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
function value_override_pretty:closure(pp)
	local param_name, code, capture = self:unwrap_closure()
	local context = ensure_context(capture)
	local inner_context = context:append(param_name)
	local is_destructure, is_rename, names, code, inner_context = typed_destructure_helper(code, inner_context)
	if is_rename then
		---@cast names string
		param_name = names
		is_destructure = false
	end

	pp:_enter()

	pp:unit(pp:_color())
	pp:unit("value.closure ")
	pp:unit(pp:_resetcolor())

	if is_destructure then
		---@cast names ArrayValue
		if names:len() == 0 then
			pp:unit(pp:_color())
			pp:unit("()")
			pp:unit(pp:_resetcolor())
		end

		for i, name in names:ipairs() do
			if i > 1 then
				pp:unit(" ")
			end
			pp:unit(name)
		end
	else
		pp:unit(param_name)
	end

	pp:unit(pp:_color())
	pp:unit(" ->")
	pp:unit(pp:_resetcolor())

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
function inferrable_term_override_pretty:pi(pp, context)
	-- extracting parameter names from the destructure of the result
	-- so that we get the name of the last parameter
	-- name of the last result is still lost
	local param_type, _, result_type, _ = self:unwrap_pi()
	context = ensure_context(context)
	local result_context = context
	local param_is_tuple_type, param_desc = as_any_tuple_type(param_type)
	local result_is_readable, param_name, _, result_body, _ = result_type:as_annotated_lambda()
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

	pp:unit(pp:_color())
	pp:unit("inferrable.\u{03A0} ")
	pp:unit(pp:_resetcolor())

	if not result_is_readable then
		pp:any(param_type, context)
	elseif param_is_tuple_type and result_is_destructure then
		---@cast param_names ArrayValue
		---@cast param_members TupleDescFlat[]
		if #param_members == 0 then
			pp:unit(pp:_color())
			pp:unit("()")
			pp:unit(pp:_resetcolor())
		else
			tuple_type_helper(pp, param_members, param_names)
		end
	elseif result_is_destructure then
		---@cast param_names ArrayValue
		-- tuple_elim on params but params aren't a tuple type???
		-- probably shouldn't happen, but here's a handler
		pp:unit(pp:_color())
		pp:unit("(")
		pp:unit(pp:_resetcolor())

		for i, name in param_names:ipairs() do
			if i > 1 then
				pp:unit(" ")
			end
			pp:unit(name)
		end

		pp:unit(pp:_color())
		pp:unit(") : ")
		pp:unit(pp:_resetcolor())

		pp:any(param_type, context)
	else
		pp:unit(param_name)

		pp:unit(pp:_color())
		pp:unit(" : ")
		pp:unit(pp:_resetcolor())

		pp:any(param_type, context)
	end

	pp:unit(pp:_color())
	pp:unit(" -> ")
	pp:unit(pp:_resetcolor())

	if not result_is_readable then
		pp:any(result_type, context)
	elseif result_is_tuple_type then
		---@cast result_members TupleDescFlat[]
		if #result_members == 0 then
			pp:unit(pp:_color())
			pp:unit("()")
			pp:unit(pp:_resetcolor())
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
function inferrable_term_override_pretty:host_function_type(pp, context)
	local param_type, result_type, _ = self:unwrap_host_function_type()
	context = ensure_context(context)
	local result_context = context
	local param_is_tuple_type, param_desc = param_type:as_host_tuple_type()
	local result_is_readable, param_name, _, result_body, _ = result_type:as_annotated_lambda()
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

	pp:unit(pp:_color())
	pp:unit("inferrable.host-\u{03A0} ")
	pp:unit(pp:_resetcolor())

	if not result_is_readable then
		pp:any(param_type, context)
	elseif param_is_tuple_type and result_is_destructure then
		---@cast param_names ArrayValue
		---@cast param_members TupleDescFlat[]
		if #param_members == 0 then
			pp:unit(pp:_color())
			pp:unit("()")
			pp:unit(pp:_resetcolor())
		else
			tuple_type_helper(pp, param_members, param_names)
		end
	elseif result_is_destructure then
		---@cast param_names ArrayValue
		-- tuple_elim on params but params aren't a tuple type???
		-- probably shouldn't happen, but here's a handler
		pp:unit(pp:_color())
		pp:unit("(")
		pp:unit(pp:_resetcolor())

		for i, name in param_names:ipairs() do
			if i > 1 then
				pp:unit(" ")
			end
			pp:unit(name)
		end

		pp:unit(pp:_color())
		pp:unit(") : ")
		pp:unit(pp:_resetcolor())

		pp:any(param_type, context)
	else
		pp:unit(param_name)

		pp:unit(pp:_color())
		pp:unit(" : ")
		pp:unit(pp:_resetcolor())

		pp:any(param_type, context)
	end

	pp:unit(pp:_color())
	pp:unit(" -> ")
	pp:unit(pp:_resetcolor())

	if not result_is_readable then
		pp:any(result_type, context)
	elseif result_is_tuple_type then
		---@cast result_members TupleDescFlat[]
		if #result_members == 0 then
			pp:unit(pp:_color())
			pp:unit("()")
			pp:unit(pp:_resetcolor())
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
	local param_type, _, result_type, _ = self:unwrap_pi()
	context = ensure_context(context)
	local result_context = context
	local param_is_tuple_type, param_desc = as_any_tuple_type(param_type)
	local result_is_readable, param_name, result_body = result_type:as_lambda()
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

	pp:unit(pp:_color())
	pp:unit("typed.\u{03A0} ")
	pp:unit(pp:_resetcolor())

	if not result_is_readable then
		pp:any(param_type, context)
	elseif param_is_tuple_type and result_is_destructure then
		---@cast param_names ArrayValue
		---@cast param_members TupleDescFlat[]
		if #param_members == 0 then
			pp:unit(pp:_color())
			pp:unit("()")
			pp:unit(pp:_resetcolor())
		else
			tuple_type_helper(pp, param_members, param_names)
		end
	elseif result_is_destructure then
		---@cast param_names ArrayValue
		-- tuple_elim on params but params aren't a tuple type???
		-- probably shouldn't happen, but here's a handler
		pp:unit(pp:_color())
		pp:unit("(")
		pp:unit(pp:_resetcolor())

		for i, name in param_names:ipairs() do
			if i > 1 then
				pp:unit(" ")
			end
			pp:unit(name)
		end

		pp:unit(pp:_color())
		pp:unit(") : ")
		pp:unit(pp:_resetcolor())

		pp:any(param_type, context)
	else
		pp:unit(param_name)

		pp:unit(pp:_color())
		pp:unit(" : ")
		pp:unit(pp:_resetcolor())

		pp:any(param_type, context)
	end

	pp:unit(pp:_color())
	pp:unit(" -> ")
	pp:unit(pp:_resetcolor())

	if not result_is_readable then
		pp:any(result_type, context)
	elseif result_is_tuple_type then
		---@cast result_members TupleDescFlat[]
		if #result_members == 0 then
			pp:unit(pp:_color())
			pp:unit("()")
			pp:unit(pp:_resetcolor())
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
	local param_type, result_type, _ = self:unwrap_host_function_type()
	context = ensure_context(context)
	local result_context = context
	local param_is_tuple_type, param_desc = param_type:as_host_tuple_type()
	local result_is_readable, param_name, result_body = result_type:as_lambda()
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

	pp:unit(pp:_color())
	pp:unit("typed.host-\u{03A0} ")
	pp:unit(pp:_resetcolor())

	if not result_is_readable then
		pp:any(param_type, context)
	elseif param_is_tuple_type and result_is_destructure then
		---@cast param_names ArrayValue
		---@cast param_members TupleDescFlat[]
		if #param_members == 0 then
			pp:unit(pp:_color())
			pp:unit("()")
			pp:unit(pp:_resetcolor())
		else
			tuple_type_helper(pp, param_members, param_names)
		end
	elseif result_is_destructure then
		---@cast param_names ArrayValue
		-- tuple_elim on params but params aren't a tuple type???
		-- probably shouldn't happen, but here's a handler
		pp:unit(pp:_color())
		pp:unit("(")
		pp:unit(pp:_resetcolor())

		for i, name in param_names:ipairs() do
			if i > 1 then
				pp:unit(" ")
			end
			pp:unit(name)
		end

		pp:unit(pp:_color())
		pp:unit(") : ")
		pp:unit(pp:_resetcolor())

		pp:any(param_type, context)
	else
		pp:unit(param_name)

		pp:unit(pp:_color())
		pp:unit(" : ")
		pp:unit(pp:_resetcolor())

		pp:any(param_type, context)
	end

	pp:unit(pp:_color())
	pp:unit(" -> ")
	pp:unit(pp:_resetcolor())

	if not result_is_readable then
		pp:any(result_type, context)
	elseif result_is_tuple_type then
		---@cast result_members TupleDescFlat[]
		if #result_members == 0 then
			pp:unit(pp:_color())
			pp:unit("()")
			pp:unit(pp:_resetcolor())
		else
			tuple_type_helper(pp, result_members)
		end
	else
		pp:any(result_body, result_context)
	end

	pp:_exit()
end

---@param pp PrettyPrint
function value_override_pretty:pi(pp)
	local param_type, _, result_type, _ = self:unwrap_pi()
	local param_is_tuple_type, param_desc = as_any_tuple_type(param_type)
	local result_is_readable, param_name, result_code, result_capture = result_type:as_closure()
	local result_context, result_is_destructure, result_is_rename, param_names, result_is_tuple_type, result_desc
	if result_is_readable then
		result_context = ensure_context(result_capture)
		result_context = result_context:append(param_name)
		result_is_destructure, result_is_rename, param_names, result_code, result_context =
			typed_destructure_helper(result_code, result_context)
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

	pp:unit(pp:_color())
	pp:unit("value.\u{03A0} ")
	pp:unit(pp:_resetcolor())

	if not result_is_readable then
		pp:any(param_type)
	elseif param_is_tuple_type and result_is_destructure then
		---@cast param_names ArrayValue
		---@cast param_members TupleDescFlat[]
		if #param_members == 0 then
			pp:unit(pp:_color())
			pp:unit("()")
			pp:unit(pp:_resetcolor())
		else
			tuple_type_helper(pp, param_members, param_names)
		end
	elseif result_is_destructure then
		---@cast param_names ArrayValue
		-- tuple_elim on params but params aren't a tuple type???
		-- probably shouldn't happen, but here's a handler
		pp:unit(pp:_color())
		pp:unit("(")
		pp:unit(pp:_resetcolor())

		for i, name in param_names:ipairs() do
			if i > 1 then
				pp:unit(" ")
			end
			pp:unit(name)
		end

		pp:unit(pp:_color())
		pp:unit(") : ")
		pp:unit(pp:_resetcolor())

		pp:any(param_type)
	else
		pp:unit(param_name)

		pp:unit(pp:_color())
		pp:unit(" : ")
		pp:unit(pp:_resetcolor())

		pp:any(param_type)
	end

	pp:unit(pp:_color())
	pp:unit(" -> ")
	pp:unit(pp:_resetcolor())

	if not result_is_readable then
		pp:any(result_type)
	elseif result_is_tuple_type then
		---@cast result_members TupleDescFlat[]
		if #result_members == 0 then
			pp:unit(pp:_color())
			pp:unit("()")
			pp:unit(pp:_resetcolor())
		else
			tuple_type_helper(pp, result_members)
		end
	else
		pp:any(result_code, result_context)
	end

	pp:_exit()
end

---@param pp PrettyPrint
function value_override_pretty:host_function_type(pp)
	local param_type, result_type, _ = self:unwrap_host_function_type()
	local param_is_tuple_type, param_desc = param_type:as_host_tuple_type()
	local result_is_readable, param_name, result_code, result_capture = result_type:as_closure()
	local result_context, result_is_destructure, result_is_rename, param_names, result_is_tuple_type, result_desc
	if result_is_readable then
		result_context = ensure_context(result_capture)
		result_context = result_context:append(param_name)
		result_is_destructure, result_is_rename, param_names, result_code, result_context =
			typed_destructure_helper(result_code, result_context)
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

	pp:unit(pp:_color())
	pp:unit("value.host-\u{03A0} ")
	pp:unit(pp:_resetcolor())

	if not result_is_readable then
		pp:any(param_type)
	elseif param_is_tuple_type and result_is_destructure then
		---@cast param_names ArrayValue
		---@cast param_members TupleDescFlat[]
		if #param_members == 0 then
			pp:unit(pp:_color())
			pp:unit("()")
			pp:unit(pp:_resetcolor())
		else
			tuple_type_helper(pp, param_members, param_names)
		end
	elseif result_is_destructure then
		---@cast param_names ArrayValue
		-- tuple_elim on params but params aren't a tuple type???
		-- probably shouldn't happen, but here's a handler
		pp:unit(pp:_color())
		pp:unit("(")
		pp:unit(pp:_resetcolor())

		for i, name in param_names:ipairs() do
			if i > 1 then
				pp:unit(" ")
			end
			pp:unit(name)
		end

		pp:unit(pp:_color())
		pp:unit(") : ")
		pp:unit(pp:_resetcolor())

		pp:any(param_type)
	else
		pp:unit(param_name)

		pp:unit(pp:_color())
		pp:unit(" : ")
		pp:unit(pp:_resetcolor())

		pp:any(param_type)
	end

	pp:unit(pp:_color())
	pp:unit(" -> ")
	pp:unit(pp:_resetcolor())

	if not result_is_readable then
		pp:any(result_type)
	elseif result_is_tuple_type then
		---@cast result_members TupleDescFlat[]
		if #result_members == 0 then
			pp:unit(pp:_color())
			pp:unit("()")
			pp:unit(pp:_resetcolor())
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
function inferrable_term_override_pretty:application(pp, context)
	local f, arg = self:unwrap_application()
	context = ensure_context(context)

	-- handle nested applications
	---@param f inferrable
	---@param arg checkable
	local function application_inner(f, arg)
		local f_is_application, f_f, f_arg = f:as_application()
		local f_is_typed, _, _, f_typed_term = f:as_typed()
		local f_is_bound_variable, f_index = false, 0
		if f_is_typed then
			f_is_bound_variable, f_index = f_typed_term:as_bound_variable()
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
				pp:unit(context:get_name(f_index))
			end

			local ok, elements = arg:as_tuple_cons()
			elements = ok and elements or arg:unwrap_host_tuple_cons()

			pp:unit(pp:_color())
			pp:unit("(")
			pp:unit(pp:_resetcolor())

			for i, arg in elements:ipairs() do
				if i > 1 then
					pp:unit(pp:_color())
					pp:unit(", ")
					pp:unit(pp:_resetcolor())
				end

				pp:any(arg, context)
			end

			pp:unit(pp:_color())
			pp:unit(")")
			pp:unit(pp:_resetcolor())
		else
			-- if we're here then the args are probably horrible
			-- add some newlines
			pp:unit(pp:_color())
			pp:unit("inferrable.apply(")
			pp:unit(pp:_resetcolor())
			pp:unit("\n")

			pp:_indent()

			pp:_prefix()
			pp:any(f, context)
			pp:unit(pp:_color())
			pp:unit(",")
			pp:unit(pp:_resetcolor())
			pp:unit("\n")

			pp:_prefix()
			pp:any(arg, context)
			pp:unit("\n")

			pp:_dedent()

			pp:_prefix()
			pp:unit(pp:_color())
			pp:unit(")")
			pp:unit(pp:_resetcolor())
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
		local f_is_bound_variable, f_index = f:as_bound_variable()

		pp:_enter()

		-- print pretty on certain conditions, or fall back to apply()
		if
			(f_is_application or (f_is_bound_variable and context:len() >= f_index))
			and (arg:is_tuple_cons() or arg:is_host_tuple_cons())
		then
			if f_is_application then
				application_inner(f_f, f_arg)
			else
				pp:unit(context:get_name(f_index))
			end

			local ok, elements = arg:as_tuple_cons()
			elements = ok and elements or arg:unwrap_host_tuple_cons()

			pp:unit(pp:_color())
			pp:unit("(")
			pp:unit(pp:_resetcolor())

			for i, arg in elements:ipairs() do
				if i > 1 then
					pp:unit(pp:_color())
					pp:unit(", ")
					pp:unit(pp:_resetcolor())
				end

				pp:any(arg, context)
			end

			pp:unit(pp:_color())
			pp:unit(")")
			pp:unit(pp:_resetcolor())
		else
			-- if we're here then the args are probably horrible
			-- add some newlines
			pp:unit(pp:_color())
			pp:unit("typed.apply(")
			pp:unit(pp:_resetcolor())
			pp:unit("\n")

			pp:_indent()

			pp:_prefix()
			pp:any(f, context)
			pp:unit(pp:_color())
			pp:unit(",")
			pp:unit(pp:_resetcolor())
			pp:unit("\n")

			pp:_prefix()
			pp:any(arg, context)
			pp:unit("\n")

			pp:_dedent()

			pp:_prefix()
			pp:unit(pp:_color())
			pp:unit(")")
			pp:unit(pp:_resetcolor())
		end

		pp:_exit()
	end

	application_inner(f, arg)
end

---@param pp PrettyPrint
---@param context AnyContext
function inferrable_term_override_pretty:tuple_type(pp, context)
	local desc = self:unwrap_tuple_type()
	context = ensure_context(context)
	local ok, members = inferrable_tuple_type_flatten(desc, context)

	pp:_enter()

	pp:unit(pp:_color())
	pp:unit("inferrable.tuple_type[")
	pp:unit(pp:_resetcolor())

	if ok then
		---@cast members TupleDescFlat[]
		tuple_type_helper(pp, members)
	else
		members = inferrable_tuple_type_hydraulicpress(desc)

		for i, f in ipairs(members) do
			if i > 1 then
				pp:unit(pp:_color())
				pp:unit(", ")
				pp:unit(pp:_resetcolor())
			end

			pp:any(f, context)
		end
	end

	pp:unit(pp:_color())
	pp:unit("]")
	pp:unit(pp:_resetcolor())

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function inferrable_term_override_pretty:host_tuple_type(pp, context)
	local desc = self:unwrap_host_tuple_type()
	context = ensure_context(context)
	local ok, members = inferrable_tuple_type_flatten(desc, context)

	pp:_enter()

	pp:unit(pp:_color())
	pp:unit("inferrable.host_tuple_type[")
	pp:unit(pp:_resetcolor())

	if ok then
		---@cast members TupleDescFlat[]
		tuple_type_helper(pp, members)
	else
		members = inferrable_tuple_type_hydraulicpress(desc)

		for i, f in ipairs(members) do
			if i > 1 then
				pp:unit(pp:_color())
				pp:unit(", ")
				pp:unit(pp:_resetcolor())
			end

			pp:any(f, context)
		end
	end

	pp:unit(pp:_color())
	pp:unit("]")
	pp:unit(pp:_resetcolor())

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function typed_term_override_pretty:tuple_type(pp, context)
	local desc = self:unwrap_tuple_type()
	context = ensure_context(context)
	local ok, members = typed_tuple_type_flatten(desc, context)

	pp:_enter()

	pp:unit(pp:_color())
	pp:unit("typed.tuple_type[")
	pp:unit(pp:_resetcolor())

	if ok then
		---@cast members TupleDescFlat[]
		tuple_type_helper(pp, members)
	else
		members = typed_tuple_type_hydraulicpress(desc)

		for i, f in ipairs(members) do
			if i > 1 then
				pp:unit(pp:_color())
				pp:unit(", ")
				pp:unit(pp:_resetcolor())
			end

			pp:any(f, context)
		end
	end

	pp:unit(pp:_color())
	pp:unit("]")
	pp:unit(pp:_resetcolor())

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function typed_term_override_pretty:host_tuple_type(pp, context)
	local desc = self:unwrap_host_tuple_type()
	context = ensure_context(context)
	local ok, members = typed_tuple_type_flatten(desc, context)

	pp:_enter()

	pp:unit(pp:_color())
	pp:unit("typed.host_tuple_type[")
	pp:unit(pp:_resetcolor())

	if ok then
		---@cast members TupleDescFlat[]
		tuple_type_helper(pp, members)
	else
		members = typed_tuple_type_hydraulicpress(desc)

		for i, f in ipairs(members) do
			if i > 1 then
				pp:unit(pp:_color())
				pp:unit(", ")
				pp:unit(pp:_resetcolor())
			end

			pp:any(f, context)
		end
	end

	pp:unit(pp:_color())
	pp:unit("]")
	pp:unit(pp:_resetcolor())

	pp:_exit()
end

---@param pp PrettyPrint
function value_override_pretty:tuple_type(pp)
	local desc = self:unwrap_tuple_type()
	local ok, members = value_tuple_type_flatten(desc)

	pp:_enter()

	pp:unit(pp:_color())
	pp:unit("value.tuple_type[")
	pp:unit(pp:_resetcolor())

	if ok then
		---@cast members TupleDescFlat[]
		tuple_type_helper(pp, members)
	else
		members = value_tuple_type_hydraulicpress(desc)

		for i, f in ipairs(members) do
			if i > 1 then
				pp:unit(pp:_color())
				pp:unit(", ")
				pp:unit(pp:_resetcolor())
			end

			pp:any(f)
		end
	end

	pp:unit(pp:_color())
	pp:unit("]")
	pp:unit(pp:_resetcolor())

	pp:_exit()
end

---@param pp PrettyPrint
function value_override_pretty:host_tuple_type(pp)
	local desc = self:unwrap_host_tuple_type()
	local ok, members = value_tuple_type_flatten(desc)

	pp:_enter()

	pp:unit(pp:_color())
	pp:unit("value.host_tuple_type[")
	pp:unit(pp:_resetcolor())

	if ok then
		---@cast members TupleDescFlat[]
		tuple_type_helper(pp, members)
	else
		members = value_tuple_type_hydraulicpress(desc)

		for i, f in ipairs(members) do
			if i > 1 then
				pp:unit(pp:_color())
				pp:unit(", ")
				pp:unit(pp:_resetcolor())
			end

			pp:any(f)
		end
	end

	pp:unit(pp:_color())
	pp:unit("]")
	pp:unit(pp:_resetcolor())

	pp:_exit()
end

---@param pp PrettyPrint
function value_override_pretty:neutral(pp)
	local desc = self:unwrap_neutral()

	pp:_enter()

	if desc:is_free() and desc:unwrap_free():is_metavariable() then
		local mt = desc:unwrap_free():unwrap_metavariable()
		pp:unit(pp:_color())
		pp:unit("\u{2A64} " .. mt.value .. ":" .. mt.usage .. "|" .. mt.block_level .. " \u{2A65}")
		pp:unit(pp:_resetcolor())
	else
		pp:unit(pp:_color())
		pp:unit("value.neutral[")
		pp:unit(pp:_resetcolor())
		pp:any(desc)
		pp:unit(pp:_color())
		pp:unit("]")
		pp:unit(pp:_resetcolor())
	end

	pp:_exit()
end

---@param pp PrettyPrint
---@param context AnyContext
function typed_term_override_pretty:tuple_element_access(pp, context)
	local subject, index = self:unwrap_tuple_element_access()
	context = ensure_context(context)
	local subject_is_bound_variable, subject_index = subject:as_bound_variable()

	if subject_is_bound_variable and context:len() >= subject_index then
		pp:_enter()

		pp:unit(context:get_name(subject_index))

		pp:unit(pp:_color())
		pp:unit(".")
		pp:unit(pp:_resetcolor())

		pp:unit(tostring(index))

		pp:_exit()
	else
		pp:record("typed.tuple_element_access", { { "subject", subject }, { "index", index } }, context)
	end
end

---@param pp PrettyPrint
---@param context AnyContext
function typed_term_override_pretty:host_intrinsic(pp, context)
	local source, _ = self:unwrap_host_intrinsic()

	pp:_enter()

	pp:unit(pp:_color())
	pp:unit("typed.host_intrinsic ")
	pp:unit(pp:_resetcolor())

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

		pp:any(source_print)
	else
		pp:any(source, context)
	end

	pp:_exit()
end

return function(args)
	typechecking_context_type = args.typechecking_context_type
	runtime_context_type = args.runtime_context_type
	DescCons = args.DescCons
	return {
		checkable_term_override_pretty = checkable_term_override_pretty,
		inferrable_term_override_pretty = inferrable_term_override_pretty,
		typed_term_override_pretty = typed_term_override_pretty,
		value_override_pretty = value_override_pretty,
		binding_override_pretty = binding_override_pretty,
	}
end
