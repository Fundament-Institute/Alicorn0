local U = require "alicorn-utils"
local metalanguage = require "metalanguage"

-- This file is a simple language built with metalanguage
-- it could be used to create tests of metalanguage that don't rely
-- on other parts of Alicorn

local eval

local function eval_passhandler(env, val)
	--print("eval pass handler", val, env)
	return true, val, env
end

local eval

---@param syntax ConstructedSyntax
---@param matcher Matcher
---@param environment Env
---@return ...
local function Eval(syntax, matcher, environment)
	return U.notail(eval(syntax, environment))
end

local evaluates = metalanguage.reducer(Eval, "evaluates")

local function eval_pairhandler(env, a, b)
	--print("in eval pairhandler", a, b, env)
	local ok, combiner, _ = a:match({
		evaluates(eval_passhandler, env),
	}, metalanguage.failure_handler, env)
	if not ok then
		return false, combiner
	end
	local ok, val, newenv = combiner:apply(b, env)
	--print("eval pair", ok, val, newenv)
	return ok, val, newenv
end

---@param env Env
---@param name string
---@return boolean
---@return any | string
local function symbolenvhandler(env, name)
	--print("symbolenvhandler(", name, env, ")")
	local res = env:get(name)
	if res ~= nil then
		return true, res
	else
		return false, "environment does not contain a binding for " .. name
	end
end

local function SymbolInEnvironment(syntax, environment)
	--print("in symbol in environment reducer", matcher.kind, matcher[1], matcher)
	return U.notail(syntax:match({
		metalanguage.issymbol(symbolenvhandler),
	}, metalanguage.failure_handler, environment))
end

local symbol_in_environment = metalanguage.reducer(SymbolInEnvironment, "symbol in env")

---@param syntax ConstructedSyntax
---@param environment Env
---@return ...
function eval(syntax, environment)
	return U.notail(syntax:match({
		symbol_in_environment(eval_passhandler, environment),
		metalanguage.isvalue(eval_passhandler),
		metalanguage.ispair(eval_pairhandler),
	}, metalanguage.failure_handler, environment))
end

---@generic T
---@param val T
---@param newenv Env
---@return boolean, T, Env
local function syntax_args_val_handler(_, val, newenv)
	return true, val, newenv
end

local function syntax_args_nil_handler(data)
	return true, false
end

---@generic T
---@param env Env
---@param a ConstructedSyntax
---@param b T
---@return boolean
---@return boolean
---@return any
---@return T
local function syntax_args_pair_handler(env, a, b)
	local ok, val, _ = a:match({
		evaluates(syntax_args_val_handler, env),
	}, metalanguage.failure_handler, nil)
	--print("args pair handler", ok, val, _, b)
	return true, true, val, b
end

---@param syntax ConstructedSyntax
---@param matcher Matcher
---@param environment Env
---@return boolean
---@return any[]
local function EvalArgs(syntax, matcher, environment)
	local args = {}
	local ok, ispair, val, tail = true, true, nil, nil
	while ok and ispair do
		ok, ispair, val, tail = syntax:match({
			metalanguage.ispair(syntax_args_pair_handler),
			metalanguage.isnil(syntax_args_nil_handler),
		}, metalanguage.failure_handler, environment)
		if not ok then
			return false, ispair
		end
		if ispair then
			args[#args + 1] = val
			syntax = tail
		end
	end
	return true, args
end

local evalargs = metalanguage.reducer(EvalArgs, "evalargs")

local primitive_applicative_mt = {
	__index = {
		apply = function(self, ops, env)
			local ok, args = ops:match({
				evalargs(metalanguage.accept_handler, env),
			}, metalanguage.failure_handler, nil)
			local res = self.fn(table.unpack(args))
			return true, U.notail(metalanguage.value(nil, nil, res)), env
		end,
	},
}

local function primitive_applicative(fn)
	return setmetatable({ fn = fn }, primitive_applicative_mt)
end

local primitive_operative_mt = {
	__index = {
		apply = function(self, ops, env)
			return U.notail(self.fn(ops, env))
		end,
	},
}

local function primitive_operative(fn)
	return setmetatable({ fn = fn }, primitive_operative_mt)
end

return {
	eval = eval,
	evalargs = evalargs,
	evaluates = evaluates,
	primitive_applicative = primitive_applicative,
	primitive_operative = primitive_operative,
}
