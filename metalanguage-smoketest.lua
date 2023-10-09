local metalang = require "metalanguage"
local testlang = require "testlanguage"
local format = require "test-format-adapter"

-- for k, v in pairs(lang) do print(k, v) end

local symbol, value, list = metalang.symbol, metalang.value, metalang.list

--[[
local code =
  list(
    symbol "+",
    value(1),
    value(2)
  )
--]]

local src = "do (val x = 6) (+ x 3)"
local code = format.read(src, "inline")

local function do_block_pair_handler(env, a, b)
	local ok, val, newenv = a:match({
		testlang.evaluates(metalang.accept_handler, env),
	}, metalang.failure_handler, nil)
	if not ok then
		return false, val
	end
	--print("do block pair handler", ok, val, newenv, b)
	return true, true, val, newenv, b
end

local function do_block_nil_handler(env)
	return true, false
end

local function do_block(syntax, env)
	local res = nil
	local ok, ispair, val, newenv, tail = true, true, nil, env, nil
	while ok and ispair do
		ok, ispair, val, newenv, tail = syntax:match({
			metalang.ispair(do_block_pair_handler),
			metalang.isnil(do_block_nil_handler),
		}, metalang.failure_handler, newenv)
		--print("do block", ok, ispair, val, newenv, tail)
		if not ok then
			return false, ispair
		end
		if ispair then
			res = val
			syntax = tail
		end
	end
	return true, res, env
end

local function val_bind(syntax, env)
	local ok, name, val = syntax:match({
		metalang.listmatch(
			metalang.accept_handler,
			metalang.issymbol(metalang.accept_handler),
			metalang.symbol_exact(metalang.accept_handler, "="),
			testlang.evaluates(metalang.accept_handler, env)
		),
	}, metalang.failure_handler, nil)
	--print("val bind", ok, name, _, val)
	if not ok then
		return false, name
	end
	return true, value(nil), env + metalang.newenv { [name] = val }
end

local env = metalang.newenv {
	["+"] = testlang.primitive_applicative(function(a, b)
		return a + b
	end),
	["do"] = testlang.primitive_operative(do_block),
	val = testlang.primitive_operative(val_bind),
}

local ok, res = testlang.eval(code, env)

print(ok, res)

print(res[1])
