
local lang = require "./metalanguage"
local format = require "./temp-format-adapter"

-- for k, v in pairs(lang) do print(k, v) end

local symbol, value, list = lang.symbol, lang.value, lang.list

--[[
local code =
  list(
    symbol "+",
    value(1),
    value(2)
  )
--]]

local src = "do (val x = 6) (+ x 3)"

local code_orig =
  list(
    symbol "do",
    list(
      symbol "val", symbol "x", symbol "=", value(6)
    ),
    list(
      symbol "+", symbol "x", value(3)
    )
  )

local code = format.read(src, "inline")

-- assert code and code_orig are equal?

local function do_block_pair_handler(env, a, b)
  local ok, val, newenv =
    a:match(
      {
        {
          kind = "Eval",
          env,
          handler = lang.accept_handler
        }
      },
      lang.failure_handler,
      nil
    )
  if not ok then return false, val end
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
    ok, ispair, val, newenv, tail =
      syntax:match(
        {
          {
            kind = "Pair",
            handler = do_block_pair_handler
          },
          {
            kind = "Nil",
            handler = do_block_nil_handler
          }
        },
        lang.failure_handler,
        newenv
      )
    --print("do block", ok, ispair, val, newenv, tail)
    if not ok then return false, ispair end
    if ispair then
      res = val
      syntax = tail
    end
  end
  return true, res, env
end

local function val_bind(syntax, env)
  local ok, name, val =
    syntax:match(
      {
        {
          kind = "ListMatch",
          {
            kind = "Symbol",
            handler = lang.accept_handler
          },
          {
            kind = "SymbolExact",
            "=",
            handler = lang.accept_handler
          },
          {
            kind = "Eval",
            env,
            handler = lang.accept_handler
          },
          handler = lang.accept_handler
        }
      },
      lang.failure_handler,
      nil
    )
  --print("val bind", ok, name, _, val)
  if not ok then return false, name end
  return true, value(nil), env + lang.newenv{[name] = val}
end

local env =
  lang.newenv {
    ["+"] = lang.primitive_applicative(function(a, b) return a + b end),
    ["do"] = lang.primitive_operative(do_block),
    val = lang.primitive_operative(val_bind)
  }

local ok, res = lang.eval(code, env)

print(ok, res)

print(res[1])
