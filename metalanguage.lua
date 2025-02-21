-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

local U = require "alicorn-utils"
local gen = require "terms-generators"

--[[
Matcher(userdata : type, results : tuple-desc) : type
Syntax : type
Literal : type
Reducer(sig : tuple-desc, res : tuple-desc) : type
Error : type
--]]

---@class MatcherKindContainer
local MatcherKind = --[[@enum MatcherKind]]
	{
		Symbol = "Symbol",
		Pair = "Pair",
		Nil = "Nil",
		Value = "Value",
		Reducible = "Reducible",
	}

---@generic T
---@alias SymbolFunc fun(u : T, s: string) : ...

---@generic T
---@alias PairFunc fun(u : T, a: ConstructedSyntax, b : ConstructedSyntax) : ...

---@generic T
---@alias NilFunc fun(u : T) : ...

---@generic T
---@alias ValueFunc fun(u : T, v : Literal) : ...

---@generic T
---@alias ReducibleFunc fun(u : T, ...) : ...

---@class Reducible
---@field reduce fun(syntax: ConstructedSyntax, matcher: Matcher) : ...

---@class Matcher
---@field kind MatcherKind
---@field handler SymbolFunc | PairFunc | NilFunc | ValueFunc | ReducibleFunc
---@field reducible Reducible?

---@class SyntaxSymbol
---@field str string
---@field span Span

--[[
issymbol : forall
	implicit userdata : type
	implicit results : tuple-desc
	handler : (forall (u : userdata, s : SyntaxSymbol) -> res : tuple-type(results)))
	->
	Matcher(userdata, results)
--]]
---@generic T
---@param handler SymbolFunc<T>
---@return Matcher
local function issymbol(handler)
	return {
		kind = MatcherKind.Symbol,
		handler = handler,
	}
end

--[[
ispair : forall
	implicit userdata : type
	implicit results : tuple-desc
	handler : (forall (u : userdata, a : Syntax, b : Syntax) -> res : tuple-type(results)))
	->
	Matcher(userdata, results)
--]]
---@generic T
---@param handler PairFunc<T>
---@return Matcher
local function ispair(handler)
	return {
		kind = MatcherKind.Pair,
		handler = handler,
	}
end

--[[
isnil : forall
	implicit userdata : type
	implicit results : tuple-desc
	handler : (forall (u : userdata) -> res : tuple-type(results)))
	->
	Matcher(userdata, results)
--]]
---@generic T
---@param handler NilFunc<T>
---@return Matcher
local function isnil(handler)
	return {
		kind = MatcherKind.Nil,
		handler = handler,
	}
end

---@generic T
---@param handler ValueFunc<T>
---@return Matcher
--[[
isvalue : forall
	implicit userdata : type
	implicit results : tuple-desc
	handler : (forall (u : userdata, v : Literal) -> res : tuple-type(results)))
	->
	Matcher(userdata, results)
--]]
local function isvalue(handler)
	return {
		kind = MatcherKind.Value,
		handler = handler,
	}
end

local function get_reducer(reducible)
	return getmetatable(reducible.reducible).reducer
end

local function dispatch_reducer(handler_mapping, default, matcher)
	if matcher.kind == MatcherKind.Reducible then
		if handler_mapping[get_reducer(matcher)] then
			return handler_mapping[get_reducer(matcher)](matcher)
		else
			return default(matcher)
		end
	else
		default(matcher)
	end
end

--[[
create_reducible : forall
	implicit userdata : type
	implicit reducer-sig : tuple-desc
	implicit reducer-res : tuple-desc
	implicit results : tuple-desc
	reducer : Reducer(reducer-sig)
	handler : (forall (u : userdata, ...vals : reducer-res ) -> res : tuple-type(results))
	...rest : reducer-sig
	->
	Matcher(userdata, results)
]]
---@generic T
---@param handler ReducibleFunc<T>
---@param ... any
---@return Matcher
local function create_reducible(self, handler, ...)
	local funcnew = {
		...,
	}

	setmetatable(funcnew, self.mt)

	local reducible = {
		kind = MatcherKind.Reducible,
		handler = handler,
		reducible = funcnew,
	}

	return reducible
end

local reducer_mt = { __call = create_reducible }

---@class ExternalError
---@field cause any
---@field span Span
---@field reducer_name string
local ExternalError = {}

local external_error_mt = {
	---@param self ExternalError
	---@return string
	__tostring = function(self)
		local message = "Lua error raised inside reducer "
			.. self.reducer_name
			.. " "
			.. (self.span and tostring(self.span) or "at unknown position")
			.. ":\n"
		local cause = tostring(self.cause)
		if cause:find("table", 1, true) == 1 then
			for k, v in
				pairs(self.cause --[[@as { [any]: any }]])
			do
				message = message .. tostring(k) --[[@as string]]
				message = message .. " = "
				message = message .. tostring(v)
				message = message .. "\n"
			end
		else
			message = message .. cause
		end
		return message
	end,
	__index = ExternalError,
}

---@param cause any
---@param span Span
---@param reducer_name string
---@return ExternalError
function ExternalError.new(cause, span, reducer_name)
	return setmetatable({
		cause = cause,
		span = span,
		reducer_name = reducer_name,
	}, external_error_mt)
end

---@param syntax ConstructedSyntax
---@param reducer_name string
---@param ok boolean
---@param err_msg any
---@param ... any
---@return boolean | any, ExternalError | any, ...
local function augment_error(syntax, reducer_name, ok, err_msg, ...)
	if not ok then
		return false, U.notail(ExternalError.new(err_msg, syntax.span, reducer_name))
	end
	-- err_msg is the first result arg otherwise
	return err_msg, ...
end

local pdump = require "pretty-printer".s
-- local function pdump(_)
-- 	return ""
-- end

---@class Reducer
---@field wrapper fun(syntax: ConstructedSyntax, matcher: Matcher) : ...
---@field create_reducible fun(handler: ReducibleFunc, ...) : Matcher

--- This _should_ be `true`.
local protect_reducer_func_calls = true

--[[
reducer : forall
	implicit storage : tuple-desc
	implicit results : tuple-desc
	defn : (forall (s : Syntax, ...extra : storage) -> (ok : bool, ...res : (if ok then results else tuple-desc-singleton(Error))))
	name : string
	->
	res : Reducer(storage, results)
]]
---@param func fun(syntax: ConstructedSyntax, ...) : boolean, ...
---@param name string
---@return Reducer
local function reducer(func, name)
	---@param syntax ConstructedSyntax
	---@param matcher Matcher
	---@return ...
	local function funcwrapper(syntax, matcher)
		if protect_reducer_func_calls then
			return augment_error(
				syntax,
				name,
				xpcall(func, U.custom_traceback, syntax, table.unpack(matcher.reducible))
			)
		else
			return func(syntax, table.unpack(matcher.reducible))
		end
	end

	local reducer = {
		wrapper = funcwrapper,
		create_reducible = create_reducible,
	}

	local funcnew_mt = {
		name = name,
		__index = {
			reduce = funcwrapper,
		},
		reducer = reducer,
	}

	reducer.mt = funcnew_mt

	setmetatable(reducer, reducer_mt)

	return reducer
end

---@param expected string
---@param symbol SyntaxSymbol
---@return boolean
---@return string?
local function symbolexacthandler(expected, symbol)
	if symbol.str == expected then
		return true
	else
		return false, "symbol is expected to be exactly " .. expected .. " but was instead " .. symbol.str
	end
end

---@param data any
---@param ... any
---@return boolean
---@return any
local function accept_handler(data, ...)
	return true, ...
end

---@param data any
---@param exception string
---@return boolean
---@return string
local function failure_handler(data, exception)
	return false, exception
end

---@param syntax ConstructedSyntax
---@param name string
---@return boolean
---@return string?
local function SymbolExact(syntax, name)
	return U.notail(syntax:match({
		issymbol(symbolexacthandler),
	}, failure_handler, name))
end

local symbol_exact = reducer(SymbolExact, "symbol exact")

---@class SyntaxError
---@field matchers Matcher[]
---@field span Span
---@field cause any
local SyntaxError = {}

function SyntaxError:__tostring()
	local message = "Syntax error at span "
		.. (self.span and tostring(self.span) or "<unknown position>")
		.. " must be acceptable for one of:\n"
	---@type string[]
	local options = {}
	for k, v in ipairs(self.matchers) do
		if v.kind == MatcherKind.Reducible then
			options[k] = v.kind .. ": " .. getmetatable(v.reducible).name
		else
			options[k] = v.kind
		end
	end
	message = message .. "[ " .. table.concat(options, ", ") .. " ]"
	message = message .. "\nbut was rejected"
	if self.cause then
		message = message .. " because:\n" .. tostring(self.cause)
	end
	return message
end

local syntax_error_mt = {
	__tostring = SyntaxError.__tostring,
}

---@param matchers Matcher[]
---@param span Span
---@param cause any
---@return SyntaxError
local function syntax_error(matchers, span, cause)
	return setmetatable({
		matchers = matchers,
		span = span,
		cause = cause,
	}, syntax_error_mt)
end

---@generic T
---@alias AccepterFunc fun(self: ConstructedSyntax, matcher: Matcher, extra : T) : ...

---@generic T
---@alias AccepterSet { Symbol: AccepterFunc<T>?, Pair:AccepterFunc<T>?, Nil:AccepterFunc<T>?, Value:AccepterFunc<T>? }

---@class ConstructedSyntax
---@field accepters AccepterSet
---@field span Span
local ConstructedSyntax = {}

--- ```
--- match : forall
--- 	self : Syntax
--- 	implicit userdata : type
--- 	implicit results : tuple-desc
--- 	matchers : List(Matcher(userdata, results))
--- 	unmatched : (forall (u : userdata) -> res : tuple-type(results))
--- 	extra : userdata
--- 	->
--- 	res : tuple-type(results)
--- ```
---@generic U
---@param matchers Matcher[] returns `T...`
---@param unmatched (fun(u : U, err: SyntaxError): ...) returns `T...`
---@param extra U
---@return ... returns `T...`
function ConstructedSyntax:match(matchers, unmatched, extra)
	if matchers.kind ~= nil then
		error("matchers must be a list of matchers (not a matcher itself)")
	end

	local lasterr = nil
	for _, matcher in ipairs(matchers) do
		if self.accepters[matcher.kind] then
			--   print("accepting primitive handler on kind", matcher.kind)
			return self.accepters[matcher.kind](self, matcher, extra)
		elseif matcher.kind == MatcherKind.Reducible then
			--   print("trying syntax reduction on kind", matcher.kind)
			local res = table.pack(matcher.reducible.reduce(self, matcher))
			if res[1] then
				--print("accepted syntax reduction")
				if not matcher.handler then
					print("missing handler for ", matcher.kind, debug.traceback())
				end
				return U.notail(matcher.handler(extra, table.unpack(res, 2, res.n)))
			end
			--print("rejected syntax reduction")
			lasterr = res[2] --[[@as any]]
		end
		-- local name = getmetatable(matcher.reducible)
		-- print("rejected syntax kind", matcher.kind, name)
	end
	return U.notail(unmatched(extra, syntax_error(matchers, self.span, lasterr)))
end

local constructed_syntax_mt = {
	__index = ConstructedSyntax,
}

---@param accepters AccepterSet
---@param span Span
---@param ... any
---@return ConstructedSyntax
local function cons_syntax(accepters, span, ...)
	if getmetatable(span) ~= require("format").span_mt then
		error(("metalanguage.cons_syntax called with non-span: %s"):format(span))
	end
	return setmetatable({ accepters = accepters, span = span, ... }, constructed_syntax_mt)
end

local pair_accepters = {
	Pair = function(self, matcher, extra)
		return U.notail(matcher.handler(extra, self[1], self[2]))
	end,
}

---@param span Span
---@param a ConstructedSyntax
---@param b ConstructedSyntax
---@return ConstructedSyntax
local function pair(span, a, b)
	return U.notail(cons_syntax(pair_accepters, span, a, b))
end

local symbol_accepters = {
	Symbol = function(self, matcher, extra)
		return U.notail(matcher.handler(extra, self[1]))
	end,
}

---@param span Span
---@param symbol SyntaxSymbol
---@return ConstructedSyntax
local function symbol_syntax(span, symbol)
	return U.notail(cons_syntax(symbol_accepters, span, symbol))
end

local value_accepters = {
	Value = function(self, matcher, extra)
		return U.notail(matcher.handler(extra, self[1]))
	end,
}

---@class SyntaxValue
---@field type string
---@field val any
---@field span Span

---@param span Span
---@param val SyntaxValue
---@return ConstructedSyntax
local function value(span, val)
	return U.notail(cons_syntax(value_accepters, span, val))
end

local nil_accepters = {
	Nil = function(self, matcher, extra)
		return U.notail(matcher.handler(extra))
	end,
}

---@param span Span
---@return ConstructedSyntax
local function new_nilval(span)
	return U.notail(cons_syntax(nil_accepters, span))
end

---@param span Span
---@param a ConstructedSyntax
---@param ... ConstructedSyntax
---@return ConstructedSyntax
local function list(span, a, ...)
	if a == nil then
		return U.notail(new_nilval(span))
	end
	return pair(span, a, list(span, ...))
end

local any = reducer(
	---@param syntax ConstructedSyntax
	---@return boolean
	---@return ConstructedSyntax
	function(syntax)
		return true, syntax
	end,
	"any"
)

---@generic T
---@param rule Matcher
---@param a ConstructedSyntax
---@param b T
---@return boolean
---@return any
---@return T
local function list_match_pair_handler(rule, a, b)
	--print("list pair handler", a, b, rule)
	local ok, val = a:match({ rule }, failure_handler, nil)
	return ok, val, b
end

---@param syntax ConstructedSyntax
---@param ... any
---@return boolean
---@return ...
local function ListMatch(syntax, ...)
	local args = {}
	local ok, err, val, tail = true, nil, true, nil
	for i, rule in ipairs({ ... }) do
		ok, val, tail = syntax:match({
			ispair(list_match_pair_handler),
		}, failure_handler, rule)
		--print("list match rule", ok, val, tail)
		if not ok then
			return false, val
		end
		args[#args + 1] = val
		syntax = tail
	end
	ok, err = syntax:match({
		isnil(accept_handler),
	}, failure_handler, nil)
	if not ok then
		return false, err
	end
	return true, table.unpack(args)
end

local listmatch = reducer(ListMatch, "list_match")

---@param syntax ConstructedSyntax
---@param ... any
---@return boolean
---@return ...
local function ListTail(syntax, ...)
	local args = {}
	local ok, err, val, tail = true, nil, true, nil
	for i, rule in ipairs({ ... }) do
		ok, val, tail = syntax:match({
			ispair(list_match_pair_handler),
		}, failure_handler, rule)
		--print("list+tail match rule", ok, val, tail)
		if not ok then
			return false, val
		end
		args[#args + 1] = val
		syntax = tail
	end
	args[#args + 1] = tail
	return true, table.unpack(args)
end

local listtail = reducer(ListTail, "list+tail")

---@generic T
---@param rule any
---@param a ConstructedSyntax
---@param b T
---@return boolean
---@return boolean|string
---@return any?
---@return any?
---@return T?
local function list_many_fold_pair_handler(rule, a, b)
	local ok, val, thread

	ok, val, thread = a:match({ rule[1] }, failure_handler, nil)
	if not ok then
		ok = a:match({ rule[2] }, failure_handler, nil)
		if ok then
			return ok, false, nil, nil, b
		else
			return ok, val
		end
	end
	return ok, true, val, thread, b
end

---@return boolean
---@return boolean
local function list_many_nil_handler()
	return true, false
end

local list_many_fold_until = reducer(
	---@generic T
	---@param syntax ConstructedSyntax
	---@param submatcher_fn fun(T, Span): Matcher
	---@param init_thread T
	---@param termination Matcher
	---@return boolean
	---@return any[]|string
	---@return T?
	---@return ConstructedSyntax?
	function(syntax, submatcher_fn, init_thread, termination)
		local vals = {}
		local ok, cont, val, thread, tail = true, true, nil, init_thread, syntax
		local nextthread = init_thread
		while ok and cont do
			thread = nextthread
			ok, cont, val, nextthread, tail = tail:match(
				{
					ispair(list_many_fold_pair_handler),
					isnil(list_many_nil_handler),
				},
				failure_handler,
				{
					submatcher_fn(thread, tail.span),
					termination,
				}
			)
			vals[#vals + 1] = val
		end
		if not ok then
			return ok, cont
		end
		return ok, vals, thread, tail
	end,
	"list_many_fold_until"
)

local list_many_fold = reducer(
	---@generic T
	---@param syntax ConstructedSyntax
	---@param submatcher_fn fun(T, Span): Matcher
	---@param init_thread T
	---@return boolean
	---@return any[]|string
	---@return T?
	function(syntax, submatcher_fn, init_thread)
		local ok, vals, thread, tail = syntax:match(
			{ list_many_fold_until(accept_handler, submatcher_fn, init_thread, nil) },
			failure_handler,
			nil
		)
		if not ok then
			return ok, vals
		end
		return ok, vals, thread
	end,
	"list_many_fold"
)

local list_many = reducer(
	---@param syntax ConstructedSyntax
	---@param submatcher Matcher
	---@return boolean
	---@return any[]|string
	function(syntax, submatcher)
		local ok, vals, thread, tail = syntax:match(
			{ list_many_fold(accept_handler, function()
				return submatcher
			end, {}) },
			failure_handler,
			nil
		)
		if not ok then
			return ok, false
		end
		return true, vals
	end,
	"list_many"
)

local oneof = reducer(
	---@param syntax ConstructedSyntax
	---@param ... Matcher
	---@return ...
	function(syntax, ...)
		return U.notail(syntax:match({ ... }, failure_handler, nil))
	end,
	"oneof"
)

local list_tail_ends = reducer(
	---@param syntax ConstructedSyntax
	---@param rule Matcher
	---@return boolean, ...
	function(syntax, rule)
		local res = { syntax:match({ rule }, failure_handler, nil) }
		local ok, err, tail = res[1], res[2], res[#res]

		if not ok then
			return false, err
		end

		ok, err = tail:match({ isnil(accept_handler) }, failure_handler, nil)
		if not ok then
			return false, err, "list tail does not end with nil"
		end

		res[#res] = nil

		return table.unpack(res)
	end,
	"list_tail_ends"
)

local constructed_syntax_type = gen.declare_foreign(gen.metatable_equality(constructed_syntax_mt), "ConstructedSyntax")
local reducer_type = gen.declare_foreign(gen.metatable_equality(reducer_mt), "Reducer")
local matcher_type = gen.declare_foreign(function(val)
	return MatcherKind[val.kind] ~= nil
end, "Matcher")

local metalanguage = {
	accept_handler = accept_handler,
	failure_handler = failure_handler,
	ispair = ispair,
	issymbol = issymbol,
	isvalue = isvalue,
	value = value,
	any = any,
	listmatch = listmatch,
	oneof = oneof,
	listtail = listtail,
	list_many = list_many,
	list_many_fold = list_many_fold,
	list_many_fold_until = list_many_fold_until,
	list_tail_ends = list_tail_ends,
	reducer = reducer,
	isnil = isnil,
	new_nilval = new_nilval,
	symbol_exact = symbol_exact,
	pair = pair,
	list = list,
	symbol = symbol_syntax,
	constructed_syntax_type = constructed_syntax_type,
	reducer_type = reducer_type,
	matcher_type = matcher_type,
}
local internals_interface = require "internals-interface"
internals_interface.metalanguage = metalanguage
return metalanguage
