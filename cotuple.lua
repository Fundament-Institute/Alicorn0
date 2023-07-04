

local types = require './typesystem'
local modules = require './modules'
local evaluator = require './alicorn-evaluator'
local metalang = require './metalanguage'

local function cotuple_construct(t, idx, val)
  if t.kind == types.cotuple_kind then
    if idx < 0 or >= #t.params then
      return false, "variant index out of bounds"
    end
    local ok, err = types.typeident(t.params[idx + 1], val.type)
    if not ok then return ok, err end
    local res = {constructor = idx, data = val.val}
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
  local ok, constructor_idx_val, constructor_arg, env = constructor_syntax:match(
    {
      metalang.listmatch(
        metalang.accept_handler,
        metalang.isvalue(metalang.accept_handler),
        evaluator.evaluates(metalang.accept_handler, env)
      )
    },
    metalang.failure_handler,
    nil
  )
  if not ok then return constructor_idx_val end
  if constructor_idx_val.type ~= types.number then return false, "cotuple construction variant must be an integer" end
  local constructor_idx = constructor_idx_val.val
  local t = cotuple_type.param[constructor_idx]
  local ok, err = types.type_ident(t, constructor_arg.type)
  if not ok then return ok, err end
  local val = {variant = constructor_idx, arg = constructor_arg.val}
  return true, {type = cotuple_type, val = val}, env
end
