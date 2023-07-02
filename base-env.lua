local environment = require './environment'
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
  local newenv = env:child_scope()
  local ok, val, newenv = syntax:match(
    {
      evaluator.block(metalang.accept_handler, newenv)
    },
    metalang.failure_handler,
    nil
  )
  if not ok then return ok, val end
  return ok, val, env:exit_child_scope(newenv)
end

local function let_bind(syntax, env)
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
  return true, types.unit_val, env:bind_local(name, val)
end


local core_operations = {
  ["+"] = evaluator.primitive_applicative(function(args) return args[1] + args[2] end, types.tuple {types.number, types.number}, types.number),
  ["-"] = evaluator.primitive_applicative(function(args) return args[1] - args[2] end, types.tuple {types.number, types.number}, types.number),
  ["*"] = evaluator.primitive_applicative(function(args) return args[1] * args[2] end, types.tuple {types.number, types.number}, types.number),
  ["/"] = evaluator.primitive_applicative(function(args) return args[1] / args[2] end, types.tuple {types.number, types.number}, types.number),
  neg = evaluator.primitive_applicative(function(args) return -args[1] end, types.tuple {types.number}, types.number),

  ["do"] = evaluator.primitive_operative(do_block),
  let = evaluator.primitive_operative(let_bind),
  ["dump-env"] = evaluator.primitive_operative(function(syntax, env) print(environment.dump_env(env)); return true, types.unit_val, env end)
}

local wrapped = {}
for k, v in pairs(core_operations) do
  wrapped[k] = {kind = "reusable", val = v}
end

local tree = treemap.build(wrapped)


-- p(tree)
local modules = require './modules'

local function create()
  local env = environment.new_env {
    nonlocals = tree
  }
  -- p(env)
  -- p(modules.mod)
  env = modules.use_mod(modules.module_mod, env)
  -- p(env)
  return env
end

return {
  create = create
}
