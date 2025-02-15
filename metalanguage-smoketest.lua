-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

local metalanguage = require "metalanguage"
local testlanguage = require "testlanguage"
local format = require "test-format-adapter"

---@class Env
---@field dict { [string]: any }
local Env = {}
local env_mt

---@param name string
---@return any
function Env:get(name)
	return self.dict[name]
end

function Env:without(name)
	---@type { [string]: any }
	local res = {}
	for k, v in pairs(self.dict) do
		if k ~= name then
			res[k] = v
		end
	end
	return setmetatable({ dict = res }, env_mt)
end

env_mt = {
	---@param self Env
	---@param other Env
	---@return Env
	__add = function(self, other)
		---@type { [string]: any }
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
	---@param self Env
	---@return string
	__tostring = function(self)
		local message = "env{"
		---@type string[]
		local fields = {}
		for k, v in pairs(self.dict) do
			fields[#fields + 1] = tostring(k) .. " = " .. tostring(v)
		end
		message = message .. table.concat(fields, ", ") .. "}"
		return message
	end,
}

---@param dict { [string]: any }
---@return Env
local function newenv(dict)
	return setmetatable({ dict = dict }, env_mt)
end

-- for k, v in pairs(lang) do print(k, v) end

local symbol, value, list = metalanguage.symbol, metalanguage.value, metalanguage.list

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

---@generic T
---@param env Env
---@param a ConstructedSyntax
---@param b T
---@return boolean
---@return boolean | string
---@return any?
---@return Env?
---@return T?
local function do_block_pair_handler(env, a, b)
	local ok, val, newenv = a:match({
		testlanguage.evaluates(metalanguage.accept_handler, env),
	}, metalanguage.failure_handler, nil)
	if not ok then
		return false, val
	end
	--print("do block pair handler", ok, val, newenv, b)
	return true, true, val, newenv, b
end

---@param env Env
---@return boolean
---@return boolean
local function do_block_nil_handler(env)
	return true, false
end

---@param syntax ConstructedSyntax
---@param env Env
---@return boolean
---@return any | string
---@return Env?
local function do_block(syntax, env)
	local res = nil
	local ok, ispair, val, newenv, tail = true, true, nil, env, nil
	while ok and ispair do
		ok, ispair, val, newenv, tail = syntax:match({
			metalanguage.ispair(do_block_pair_handler),
			metalanguage.isnil(do_block_nil_handler),
		}, metalanguage.failure_handler, newenv)
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

---@param syntax ConstructedSyntax
---@param env Env
---@return boolean
---@return ConstructedSyntax | string
---@return Env?
local function val_bind(syntax, env)
	local ok, symbol, val = syntax:match({
		metalanguage.listmatch(
			metalanguage.accept_handler,
			metalanguage.issymbol(metalanguage.accept_handler),
			metalanguage.symbol_exact(metalanguage.accept_handler, "="),
			testlanguage.evaluates(metalanguage.accept_handler, env)
		),
	}, metalanguage.failure_handler, nil)
	--print("val bind", ok, name, _, val)
	if not ok then
		return false, symbol.str
	end
	return true, value(nil), env + newenv({ [symbol.str] = val })
end

local env = newenv {
	["+"] = testlanguage.primitive_applicative(function(a, b)
		return a + b
	end),
	["do"] = testlanguage.primitive_operative(do_block),
	val = testlanguage.primitive_operative(val_bind),
}

local ok, res = testlanguage.eval(code, env)

print(ok, res)

print(res[1])
