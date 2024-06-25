--[[
Matcher(userdata : type, results : tuple-def) : type
Syntax : type
Literal : type
Reducer(sig : tuple-def, res : tuple-def) : type
Error : type
--]]

local matcher_kinds = {
	Symbol = true,
	Pair = true,
	Nil = true,
	Value = true,
	Reducible = true,
}

---@alias HandlerFn fun(a : any, b : any?, c : any?) : any

---@param handler HandlerFn
---@return table
--[[
issymbol : forall
	implicit userdata : type
	implicit results : tuple-def
	handler : (forall (u : userdata, s : string) -> res : tuple-type(results)))
	->
	Matcher(userdata, results)
--]]
local function issymbol(handler)
	return {
		kind = "Symbol",
		handler = handler,
	}
end

---@param handler HandlerFn
---@return table
--[[
ispair : forall
	implicit userdata : type
	implicit results : tuple-def
	handler : (forall (u : userdata, a : Syntax, b : Syntax) -> res : tuple-type(results)))
	->
	Matcher(userdata, results)
--]]
local function ispair(handler)
	return {
		kind = "Pair",
		handler = handler,
	}
end

---@param handler HandlerFn
---@return table
--[[
isnil : forall
	implicit userdata : type
	implicit results : tuple-def
	handler : (forall (u : userdata) -> res : tuple-type(results)))
	->
	Matcher(userdata, results)
--]]
local function isnil(handler)
	return {
		kind = "Nil",
		handler = handler,
	}
end

---@param handler HandlerFn
---@return table
--[[
isvalue : forall
	implicit userdata : type
	implicit results : tuple-def
	handler : (forall (u : userdata, v : Literal) -> res : tuple-type(results)))
	->
	Matcher(userdata, results)
--]]
local function isvalue(handler)
	return {
		kind = "Value",
		handler = handler,
	}
end

local function get_reducer(reducible)
	return getmetatable(reducible.reducible).reducer
end

local function dispatch_reducer(handler_mapping, default, matcher)
	if matcher.kind == "Reducible" then
		if handler_mapping[get_reducer(matcher)] then
			return handler_mapping[get_reducer(matcher)](matcher)
		else
			return default(matcher)
		end
	else
		default(matcher)
	end
end

---@class Reducible
---@field kind string
---@field handler HandlerFn
---@field reducible any

---@param handler HandlerFn
---@param ... any
---@return Reducible
--[[
create_reducible : forall
	implicit userdata : type
	implicit reducer-sig : tuple-def
	implicit reducer-res : tuple-def
	implicit results : tuple-def
	reducer : Reducer(reducer-sig)
	handler : (forall (u : userdata, ...vals : reducer-res ) -> res : tuple-type(results))
	...rest : reducer-sig
	->
	Matcher(userdata, results)
]]
local function create_reducible(self, handler, ...)
	local funcnew = {
		...,
	}

	setmetatable(funcnew, self.mt)

	local reducible = {
		kind = "Reducible",
		handler = handler,
		reducible = funcnew,
	}

	return reducible
end

local reducer_mt = { __call = create_reducible }

---@class ExternalError
---@field cause any
---@field anchor any
---@field reducer_name string
local ExternalError = {}

local external_error_mt = {
	__tostring = function(self)
		local message = "Lua error raised inside reducer "
			.. self.reducer_name
			.. " "
			.. (self.anchor and tostring(self.anchor) or "at unknown position")
			.. ":\n"
			.. tostring(self.cause)
		return message
	end,
	__index = ExternalError,
}

---@param cause any
---@param anchor any
---@param reducer_name any
---@return ExternalError
function ExternalError.new(cause, anchor, reducer_name)
	return setmetatable({
		anchor = anchor,
		cause = cause,
		reducer_name = reducer_name,
	}, external_error_mt)
end

---@param syntax any
---@param reducer_name string
---@param ok boolean
---@param err_msg any
---@param ... any
---@return boolean | any
---@return ExternalError | any
local function augment_error(syntax, reducer_name, ok, err_msg, ...)
	if not ok then
		return false, ExternalError.new(err_msg, syntax.anchor, reducer_name)
	end
	-- err_msg is the first result arg otherwise
	return err_msg, ...
end

local pdump = require "pretty-print".dump
local tag = (require "./utils").tag

---@param err table | string
---@return table | string
local function custom_traceback(err)
	if type(err) == "table" then
		return err
	end
	local s = err
	local i = 3
	local info = debug.getinfo(i, "Sfln")
	while info ~= nil do
		if info.func == tag then
			local _, name = debug.getlocal(i, 1)
			local _, tag = debug.getlocal(i, 2)
			local _, fn = debug.getlocal(i, 3)
			--i = i + 1
			--info = debug.getinfo(i, "Sfln")
			s = s .. string.format("\n%s [%s:%d] (%s)", name, info.short_src, info.currentline, pdump(tag))
		else
			local name = info.name or string.format("<%s:%d>", info.short_src, info.linedefined)
			local args = {}
			local j = 1
			local arg, v = debug.getlocal(i, j)
			while arg ~= nil do
				table.insert(args, (type(v) == "table") and "<" .. arg .. ":table>" or string.sub(tostring(v), 1, 12))
				j = j + 1
				arg, v = debug.getlocal(i, j)
			end

			--s = s .. string.format("\n%s [%s:%d] (%s)", name, info.short_src, info.currentline, table.concat(args,","))
			s = s .. string.format("\n%s [%s:%d]", name, info.short_src, info.currentline)
		end
		i = i + 1
		info = debug.getinfo(i, "Sfln")
	end

	return s
end

---@class Reducer
---@field wrapper fun(syntax: any, matcher: Reducible)

---@param func fun(syntax: any, ...)
---@param name any
---@return table
--[[
reducer : forall
	implicit storage : tuple-def
	implicit results : tuple-def
	defn : (forall (s : Syntax, ...extra : storage) -> (ok : bool, ...res : (if ok then results else tuple-def-singleton(Error))))
	name : string
	->
	res : Reducer(storage, results)
]]
local function reducer(func, name)
	local function funcwrapper(syntax, matcher)
		return augment_error(syntax, name, xpcall(func, custom_traceback, syntax, table.unpack(matcher.reducible)))
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

---@class Env
---@field dict { [any]: any }
local Env = {}
local env_mt

---comment
---@param name any
---@return any
function Env:get(name)
	return self.dict[name]
end

function Env:without(name)
	local res = {}
	for k, v in pairs(self.dict) do
		if k ~= name then
			res[k] = v
		end
	end
	return setmetatable({ dict = res }, env_mt)
end

env_mt = {
	__add = function(self, other)
		local res = {}
		for k, v in pairs(self.dict) do
			res[k] = v
		end
		for k, v in pairs(other.dict) do
			if res[k] ~= nil then
				error("names in environments being merged must be disjoint, but both environments have " .. k)
			end
			res[k] = v
		end
		return setmetatable({ dict = res }, env_mt)
	end,
	__index = Env,
	__tostring = function(self)
		local message = "env{"
		local fields = {}
		for k, v in pairs(self.dict) do
			fields[#fields + 1] = tostring(k) .. " = " .. tostring(v)
		end
		message = message .. table.concat(fields, ", ") .. "}"
		return message
	end,
}

---@param dict any
---@return Env
local function newenv(dict)
	return setmetatable({ dict = dict }, env_mt)
end

local function symbolenvhandler(env, name)
	--print("symbolenvhandler(", name, env, ")")
	local res = env:get(name)
	if res ~= nil then
		return true, res
	else
		return false, "environment does not contain a binding for " .. name
	end
end

local function symbolexacthandler(expected, name)
	if name == expected then
		return true
	else
		return false, "symbol is expected to be exactly " .. expected .. " but was instead " .. name
	end
end

local function accept_handler(data, ...)
	return true, ...
end
local function failure_handler(data, exception)
	return false, exception
end

local function SymbolInEnvironment(syntax, environment)
	--print("in symbol in environment reducer", matcher.kind, matcher[1], matcher)
	return syntax:match({
		issymbol(symbolenvhandler),
	}, failure_handler, environment)
end

local function SymbolExact(syntax, symbol)
	return syntax:match({
		issymbol(symbolexacthandler),
	}, failure_handler, symbol)
end

local symbol_in_environment = reducer(SymbolInEnvironment, "symbol in env")

local symbol_exact = reducer(SymbolExact, "symbol exact")

local syntax_error_mt = {
	__tostring = function(self)
		local message = "Syntax error at anchor "
			.. (self.anchor and tostring(self.anchor) or "<unknown position>")
			.. " must be acceptable for one of:\n"
		local options = {}
		for k, v in ipairs(self.matchers) do
			if v.kind == "Reducible" then
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
	end,
}

local function syntax_error(matchers, anchor, cause)
	return setmetatable({
		matchers = matchers,
		anchor = anchor,
		cause = cause,
	}, syntax_error_mt)
end

---@class ConstructedSyntax
---@field accepters table
---@field anchor table
local ConstructedSyntax = {}

--[[
match : forall
	self : Syntax
	implicit userdata : type
	implicit results : tuple-def
	matchers : List(Matcher(userdata, results))
	unmatched : (forall (u : userdata) -> res : tuple-type(results))
	extra : userdata
	->
	res : tuple-type(results)
]]
function ConstructedSyntax:match(matchers, unmatched, extra)
	if matchers.kind then
		print(debug.traceback())
	end
	local lasterr = nil
	for _, matcher in ipairs(matchers) do
		if self.accepters[matcher.kind] then
			--   print("accepting primitive handler on kind", matcher.kind)
			return self.accepters[matcher.kind](self, matcher, extra)
		elseif matcher.kind == "Reducible" then
			--   print("trying syntax reduction on kind", matcher.kind)
			local res = { matcher.reducible.reduce(self, matcher) }
			if res[1] then
				--print("accepted syntax reduction")
				if not matcher.handler then
					print("missing handler for ", matcher.kind, debug.traceback())
				end
				return matcher.handler(extra, table.unpack(res, 2))
			end
			--print("rejected syntax reduction")
			lasterr = res[2]
		end
		-- local name = getmetatable(matcher.reducible)
		-- print("rejected syntax kind", matcher.kind, name)
	end
	return unmatched(extra, syntax_error(matchers, self.anchor, lasterr))
end

local constructed_syntax_mt = {
	__index = ConstructedSyntax,
}

---@param accepters table
---@param anchor table
---@param ... any
---@return ConstructedSyntax
local function cons_syntax(accepters, anchor, ...)
	return setmetatable({ accepters = accepters, anchor = anchor, ... }, constructed_syntax_mt)
end

local pair_accepters = {
	Pair = function(self, matcher, extra)
		return matcher.handler(extra, self[1], self[2])
	end,
}

local function pair(anchor, a, b)
	return cons_syntax(pair_accepters, anchor, a, b)
end

local symbol_accepters = {
	Symbol = function(self, matcher, extra)
		return matcher.handler(extra, self[1])
	end,
}

local function symbol(anchor, name)
	return cons_syntax(symbol_accepters, anchor, name)
end

local value_accepters = {
	Value = function(self, matcher, extra)
		return matcher.handler(extra, self[1])
	end,
}

local function value(anchor, val)
	return cons_syntax(value_accepters, anchor, val)
end

local nil_accepters = {
	Nil = function(self, matcher, extra)
		return matcher.handler(extra)
	end,
}

local nilval = cons_syntax(nil_accepters)

local function list(a, ...)
	if a == nil then
		return nilval
	end
	return pair(a, list(...))
end

local eval

local vau_mt = {
	__index = {
		apply = function(self, ops, env)
			local bodyenv = self.params:argmatch(ops) + self.envparam:argmatch(env)
			local bodycode = self.body
			local expr
			local res
			while bodycode ~= unit do
				expr, bodycode = bodycode[1], bodycode[2]
				res, bodyenv = eval(expr, bodyenv)
			end
			return { kind = "value", res }
		end,
	},
}

local function list_match_pair_handler(rule, a, b)
	--print("list pair handler", a, b, rule)
	local ok, val = a:match({ rule }, failure_handler, nil)
	return ok, val, b
end

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

local list_many

local function list_many_threaded_pair_handler(rule, a, b)
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

local function list_many_nil_handler()
	return true, false
end

local list_many_threaded_until = reducer(function(syntax, submatcher_fn, init_thread, termination)
	local vals = {}
	local ok, cont, val, thread, tail = true, true, nil, init_thread, syntax
	local nextthread = init_thread
	while ok and cont do
		thread = nextthread
		ok, cont, val, nextthread, tail = tail:match({
			ispair(list_many_threaded_pair_handler),
			isnil(list_many_nil_handler),
		}, failure_handler, { submatcher_fn(thread), termination })
		vals[#vals + 1] = val
	end
	if not ok then
		return ok, cont
	end
	return true, vals, thread, tail
end, "list_many_threaded_until")

local list_many_threaded = reducer(function(syntax, submatcher_fn, init_thread)
	local ok, vals, thread, tail = syntax:match(
		{ list_many_threaded_until(accept_handler, submatcher_fn, init_thread, nil) },
		failure_handler,
		nil
	)
	if not ok then
		return ok, false
	end
	return ok, vals, thread
end, "list_many_threaded")

list_many = reducer(function(syntax, submatcher)
	local ok, vals, thread, tail = syntax:match(
		{ list_many_threaded(accept_handler, function(...)
			return submatcher
		end, {}) },
		failure_handler,
		nil
	)
	if not ok then
		return ok, false
	end
	return true, vals
end, "list_many")

local oneof = reducer(function(syntax, ...)
	return syntax:match({ ... }, failure_handler, nil)
end, "oneof")

local list_tail_ends = reducer(function(syntax, rule)
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
end, "list_tail_ends")

local gen = require "./terms-generators"
local constructed_syntax_type = gen.declare_foreign(gen.metatable_equality(constructed_syntax_mt))
local reducer_type = gen.declare_foreign(gen.metatable_equality(reducer_mt))
local matcher_type = gen.declare_foreign(function(val)
	return matcher_kinds[val.kind]
end)

local metalanguage = {
	newenv = newenv,
	accept_handler = accept_handler,
	failure_handler = failure_handler,
	ispair = ispair,
	issymbol = issymbol,
	isvalue = isvalue,
	value = value,
	listmatch = listmatch,
	oneof = oneof,
	listtail = listtail,
	list_many = list_many,
	list_many_threaded = list_many_threaded,
	list_many_threaded_until = list_many_threaded_until,
	list_tail_ends = list_tail_ends,
	reducer = reducer,
	isnil = isnil,
	nilval = nilval,
	symbol_exact = symbol_exact,
	pair = pair,
	list = list,
	symbol = symbol,
	symbol_in_environment = symbol_in_environment,
	constructed_syntax_type = constructed_syntax_type,
	reducer_type = reducer_type,
	matcher_type = matcher_type,
}
local internals_interface = require "./internals-interface"
internals_interface.metalanguage = metalanguage
return metalanguage
