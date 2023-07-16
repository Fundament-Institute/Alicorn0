local environment = require './environment'
local treemap = require './lazy-prefix-tree'
local evaluator = require './alicorn-evaluator'
local types = require './typesystem'
local metalang = require './metalanguage'
local utils = require './reducer-utils'

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
  local ok, name, bind =
    syntax:match(
      {
        metalang.listmatch(
          metalang.accept_handler,
          metalang.issymbol(metalang.accept_handler),
          metalang.symbol_exact(metalang.accept_handler, "="),
          evaluator.evaluates(utils.accept_with_env, env)
        )
      },
      metalang.failure_handler,
      nil
    )
  -- print("val bind", ok, name, bind)
  -- p(bind)
  if not ok then return false, name end
  return true, types.unit_val, bind.env:bind_local(name, bind.val)
end

local basic_fn_kind = {
  kind_name = "basic_fn_kind",
  type_name = function() return "basic_fn" end,
  duplicable = function() return true end,
  discardable = function() return true end,
}

local basic_fn_type = {kind = basic_fn_kind, params = {}}

evaluator.define_operate(
  basic_fn_kind,
  function(self, operands, env)
    local ok, args, env = operands:match(
      {
        evaluator.collect_tuple(metalang.accept_handler, env)
      },
      metalang.failure_handler,
      nil
    )
    if not ok then return ok, args end
    if #args.type.params ~= #self.val.argnames then return false, "argument count mismatch" end
    local bindings = {}
    for i = 1, #args.type.params do
      bindings[self.val.argnames[i]] = environment.new_store{type = args.type.params[i], val = args.val[i]}
    end
    local callenv = environment.new_env {
      locals = treemap.build(bindings),
      nonlocals = self.val.enclosing_bindings,
      carrier = env.carrier,
      perms = self.val.enclosing_perms
    }
    local ok, res, resenv = self.val.body:match(
      {
        evaluator.block(metalang.accept_handler, callenv)
      },
      metalang.failure_handler,
      nil
    )
    if not ok then return ok, res end
    return ok, res, environment.new_env {locals = env.locals, nonlocals = env.nonlocals, carrier = resenv.carrier, perms = env.perms}

end)

local function basic_fn(syntax, env)
  local ok, args, body = syntax:match(
    {
      metalang.ispair(metalang.accept_handler)
    },
    metalang.failure_handler,
    nil
  )
  if not ok then return false, args end
  -- print "defining function"
  -- p(args)
  -- p(body)
  local ok, names = args:match(
    {
      metalang.list_many(metalang.accept_handler, metalang.issymbol(metalang.accept_handler))
    },
    metalang.failure_handler,
    nil
  )
  if not ok then return ok, names end
  local defn = {
    enclosing_bindings = env.bindings,
    enclosing_perms = env.perms,
    body = body,
    argnames = names,
  }
  return true, {type = basic_fn_type, val = defn}, env
end

local function tuple_type_impl(syntax, env)
  local ok, typeargs, env = syntax:match(
    {
      evaluator.collect_tuple(metalang.accept_handler, env)
    },
    metalang.failure_handler,
    nil
  )
  if not ok then return ok, typeargs end
  for i, t in ipairs(typeargs.type.params) do
    if t ~= types.type then
      return false, "tuple-type was provided something that wasn't a type"
    end
  end
  return true, {type = types.type, val = types.tuple(typeargs.val)}, env
end
local function tuple_of_impl(syntax, env)
  local ok, components, env = syntax:match(
    {
      evaluator.collect_tuple(metalang.accept_handler, env)
    },
    metalang.failure_handler,
    nil
  )
  if not ok then return ok, components end
  return true, components, env
end

local core_operations = {
  ["+"] = evaluator.primitive_applicative(function(args) return args[1] + args[2] end, types.tuple {types.number, types.number}, types.number),
  ["-"] = evaluator.primitive_applicative(function(args) return args[1] - args[2] end, types.tuple {types.number, types.number}, types.number),
  ["*"] = evaluator.primitive_applicative(function(args) return args[1] * args[2] end, types.tuple {types.number, types.number}, types.number),
  ["/"] = evaluator.primitive_applicative(function(args) return args[1] / args[2] end, types.tuple {types.number, types.number}, types.number),
  neg = evaluator.primitive_applicative(function(args) return -args[1] end, types.tuple {types.number}, types.number),

  ["<"] = evaluator.primitive_applicative(function(args)
    return { variant = (args[1] < args[2]) and 1 or 0, arg = types.unit_val }
  end, types.tuple {types.number, types.number}, types.cotuple({types.unit, types.unit})),

  ["do"] = evaluator.primitive_operative(do_block),
  let = evaluator.primitive_operative(let_bind),
  ["dump-env"] = evaluator.primitive_operative(function(syntax, env) print(environment.dump_env(env)); return true, types.unit_val, env end),
  ["basic-fn"] = evaluator.primitive_operative(basic_fn),
  tuple = evaluator.primitive_operative(tuple_type_impl),
  ["tuple-of"] = evaluator.primitive_operative(tuple_of_impl),
}

local wrapped = {}
for k, v in pairs(core_operations) do
  wrapped[k] = {kind = "reusable", val = v}
end

local tree = treemap.build(wrapped)


-- p(tree)
local modules = require './modules'
local cotuple = require './cotuple'

local function create()
  local env = environment.new_env {
    nonlocals = tree
  }
  -- p(env)
  -- p(modules.mod)
  env = modules.use_mod(modules.module_mod, env)
  env = modules.use_mod(cotuple.cotuple_module, env)
  -- p(env)
  return env
end

return {
  create = create
}
