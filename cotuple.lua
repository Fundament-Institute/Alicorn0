

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
        evaluator.evaluates(function(_, val, env) return true, {val = val, env = env} end, env)
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
  local ok, subject_syntax, tail = syntax:match(
    {
      metalang.ispair(metalang.accept_handler)
    },
    metalang.failure_handler,
    nil
  )
  if not ok then return ok, subject_syntax end
  local ok, subject, env = subject_syntax:match(
    {
      evaluator.evaluates(metalang.accept_handler, env)
    },
    metalang.failure_handler,
    nil
  )
  if not ok then return ok, subject end
  if subject.type.kind ~= types.cotuple_kind then
    return false, "dispatch subject must be a cotuple"
  end
  local found_variant, clause = false, nil
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
  local ok, name_syntax, consequent_syntax = clause:match(
    {
      metalang.ispair(metalang.accept_handler)
    },
    metalang.failure_handler,
    nil
  )
  if not ok then return ok, name_syntax end
  local ok, name = name_syntax:match(
    {
      metalang.issymbol(metalang.accept_handler)
    },
    metalang.failure_handler,
    nil
  )
  if not ok then return ok, name end
  local ok, consequent, emptytail = consequent_syntax:match(
    {
      metalang.ispair(metalang.accept_handler)
    },
    metalang.failure_handler,
    nil
  )
  if not ok then return ok, consequent end
  local ok, err = emptytail:match({metalang.isnil(metalang.accept_handler)}, metalang.failure_handler, nil)
  if not ok then return ok, err end
  env = env:bind_local(name, {val = subject.val.arg, type = subject.type.params[subject.val.variant + 1]})
  return consequent:match({evaluator.evaluates(metalang.accept_handler, env)}, metalang.failure_handler, nil)
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
