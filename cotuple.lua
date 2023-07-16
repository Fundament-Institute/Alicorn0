

local types = require './typesystem'
local modules = require './modules'
local evaluator = require './alicorn-evaluator'
local metalang = require './metalanguage'

local p = require 'pretty-print'.prettyPrint

local function cotuple_construct(t, idx, val)
  if t.kind == types.cotuple_kind then
    if idx < 0 or idx >= #t.params then
      return false, "variant index out of bounds"
    end
    local ok, err = types.typeident(t.params[idx + 1], val.type)
    if not ok then return ok, err end
    local res = {variant = idx, arg = val.val}
    return true, {type = t, val = res}
  end
  return false, "cotuple construction must only be on cotuple kinds"
end

local function new_cotuple_op_impl(syntax, env)
  local ok, cotuple_type_syntax, constructor_syntax = syntax:match(
    {
      metalang.ispair(metalang.accept_handler)
    },
    metalang.failure_handler,
    nil
  )
  if not ok then return ok, cotuple_type_syntax end
  local ok, cotuple_type_val, env = cotuple_type_syntax:match(
    {
      evaluator.evaluates(metalang.accept_handler, env)
    },
    metalang.failure_handler,
    nil
  )
  if cotuple_type_val.type ~= types.type then return false, "first argument of cotuple construction must evaluate to a type" end
  local cotuple_type = cotuple_type_val.val
  if cotuple_type.kind ~= types.cotuple_kind then return false, "the first argument of cotuple construction must evaluate to a cotuple type" end
  if not ok then return ok, cotuple_type end
  local ok, constructor_idx_val, constructor_arg = constructor_syntax:match(
    {
      metalang.listmatch(
        metalang.accept_handler,
        metalang.isvalue(metalang.accept_handler),
        evaluator.evaluates(metalang.eval_handler, env)
      )
    },
    metalang.failure_handler,
    nil
  )
  if not ok then return ok, constructor_idx_val end
  if constructor_idx_val.type ~= types.number then return false, "cotuple construction variant must be an integer" end
  local constructor_idx = constructor_idx_val.val
  local t = cotuple_type.params[constructor_idx + 1]
  local ok, err = types.typeident(t, constructor_arg.val.type)
  if not ok then return ok, err end
  local val = {variant = constructor_idx, arg = constructor_arg.val.val}
  return true, {type = cotuple_type, val = val}, constructor_arg.env
end

local function cotuple_type_impl(syntax, env)
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
      return false, "Cotuple-type was provided something that wasn't a type"
    end
  end
  return true, {type = types.type, val = types.cotuple(typeargs.val)}, env
end

local function cotuple_dispatch_impl(syntax, env)
  -- TODO: do we *want* subject evaluation to affect env in the enclosing(outer) scope?
  local ok, subject_eval, tail = syntax:match(
    {
      metalang.listtail(
        metalang.accept_handler,
        evaluator.evaluates(metalang.eval_handler, env)
      )
    },
    metalang.failure_handler,
    nil
  )
  if not ok then return ok, subject end
  local subject, env = subject_eval.val, subject_eval.env
  if subject.type.kind ~= types.cotuple_kind then
    return false, "dispatch subject must be a cotuple"
  end
  local clause = nil
  -- skip clauses until the relevant one
  for i = 0, subject.val.variant do
    ok, clause, tail = tail:match(
      {
        metalang.ispair(metalang.accept_handler)
      },
      metalang.failure_handler,
      nil
    )
    if not ok then return ok, clause end
  end
  local ok, name, tail = clause:match(
    {
      metalang.listtail(
        metalang.accept_handler,
        metalang.issymbol(metalang.accept_handler)
      )
    },
    metalang.failure_handler,
    nil
  )
  if not ok then return ok, name end
  -- create child scope
  local childenv = env:child_scope()
  -- bind local inchild scope
  childenv = childenv:bind_local(name, {val = subject.val.arg, type = subject.type.params[subject.val.variant + 1]})
  -- eval consequent in child scope
  local ok, val_eval = tail:match(
    {
      evaluator.block(metalang.eval_handler, childenv)
    },
    metalang.failure_handler,
    nil
  )
  if not ok then return ok, val_eval end
  local val, childenv = val_eval.val, val_eval.env
  -- exit child scope with result of evaluation
  return ok, val, env:exit_child_scope(childenv)
end

local cotuple_module = modules.build_mod {
  ["cotuple-construct"] = evaluator.primitive_operative(new_cotuple_op_impl),
  ["cotuple-type"] = evaluator.primitive_operative(cotuple_type_impl),
  ["cotuple-dispatch"] = evaluator.primitive_operative(cotuple_dispatch_impl)
}

return {
  cotuple_construct = cotuple_construct,
  cotuple_module = cotuple_module.val,
}
