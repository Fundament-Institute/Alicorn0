local env = require './environment'
local treemap = require './lazy-prefix-tree'
local evaluator = require './alicorn-evaluator'
local types = require './typesystem'
local metalang = require './metalanguage'

local p = require 'pretty-print'.prettyPrint

local function do_block_pair_handler(env, a, b)
  local ok, val, newenv =
    a:match(
      {
        evaluator.evaluates(metalang.accept_handler, env)
      },
      metalang.failure_handler,
      nil
    )
  if not ok then return false, val end
  --print("do block pair handler", ok, val, newenv, b)
  return true, true, val, newenv, b
end

local function do_block_nil_handler(env)
  return true, false, nil, env
end

local function do_block(syntax, env)
  local res = nil
  local ok, ispair, val, newenv, tail = true, true, nil, env:child_scope(), nil
  -- print "starting do block"
  -- p(newenv)
  while ok and ispair do
    ok, ispair, val, newenv, tail =
      syntax:match(
        {
          metalang.ispair(do_block_pair_handler),
          metalang.isnil(do_block_nil_handler)
        },
        metalang.failure_handler,
        newenv
      )
    -- print "finished one expr in do block"
    -- p(newenv)
    --print("do block", ok, ispair, val, newenv, tail)
    if not ok then return false, ispair end
    if ispair then
      res = val
      syntax = tail
    end
  end
  return true, res, env:exit_child_scope(newenv)
end

local function val_bind(syntax, env)
  local ok, name, val =
    syntax:match(
      {
        metalang.listmatch(
          metalang.accept_handler,
          metalang.issymbol(metalang.accept_handler),
          metalang.symbol_exact(metalang.accept_handler, "="),
          evaluator.evaluates(metalang.accept_handler, env)
        )
      },
      metalang.failure_handler,
      nil
    )
  --print("val bind", ok, name, _, val)
  if not ok then return false, name end
  return true, metalang.value(nil), env:bind_local(name, val)
end

local core_operations = {
  ["+"] = evaluator.primitive_applicative(function(args) return args[1] + args[2] end, types.tuple {types.number, types.number}, types.number),
  ["-"] = evaluator.primitive_applicative(function(args) return args[1] - args[2] end, types.tuple {types.number, types.number}, types.number),
  ["*"] = evaluator.primitive_applicative(function(args) return args[1] * args[2] end, types.tuple {types.number, types.number}, types.number),
  ["/"] = evaluator.primitive_applicative(function(args) return args[1] / args[2] end, types.tuple {types.number, types.number}, types.number),
  neg = evaluator.primitive_applicative(function(args) return -args[1] end, types.tuple {types.number}, types.number),

  ["do"] = evaluator.primitive_operative(do_block),
  val = evaluator.primitive_operative(val_bind),
}

local wrapped = {}
for k, v in pairs(core_operations) do
  wrapped[k] = {kind = "reusable", val = v}
end

local tree = treemap.build(wrapped)


-- p(tree)

local function create()
  return env.new_env {
    nonlocals = tree
  }
end

return {
  create = create
}
