local terms = require './terms'
local runtime_context = terms.runtime_context
local typechecking_context = terms.typechecking_context
local checkable_term = terms.checkable_term
local inferrable_term = terms.inferrable_term
local typed_term = terms.typed_term
local free = terms.free
local quantity = terms.quantity
local visibility = terms.visibility
local purity = terms.purity
local result_info = terms.result_info
local value = terms.value
local neutral_value = terms.neutral_value

local gen = require './terms-generators'
local map = gen.declare_map
local array = gen.declare_array

--[[
local function extract_value_metavariable(value) -- -> Option<metavariable>
  if value.kind == "value_neutral" and value.neutral.kind == "neutral_value_free" and value.neutral.free.kind == "free_metavariable" then
    return value.neutral.free.metavariable
  end
  return nil
end

local is_value = gen.metatable_equality(value)

local function unify(
    first_value,
    params,
    variant,
    second_value)
  -- -> unified value,
  if first_value == second_value then
    return first_value
  end

  local first_mv = extract_value_metavariable(first_value)
  local second_mv = extract_value_metavariable(second_value)

  if first_mv and second_mv then
    first_mv:bind_metavariable(second_mv)
    return first_mv:get_canonical()
  elseif first_mv then
    return first_mv:bind_value(second_value)
  elseif second_mv then
    return second_mv:bind_value(first_value)
  end

  if first_value.kind ~= second_value.kind then
    error("can't unify values of kinds " .. first_value.kind .. " and " .. second_value.kind)
  end

  local unified_args = {}
  local prefer_left = true
  local prefer_right = true
  for i, v in ipairs(params) do
    local first_arg = first_value[v]
    local second_arg = second_value[v]
    if is_value(first_arg) then
      local u = first_arg:unify(second_arg)
      unified_args[i] = u
      prefer_left = prefer_left and u == first_arg
      prefer_right = prefer_right and u == second_arg
    elseif first_arg == second_arg then
      unified_args[i] = first_arg
    else
      p("unify args", first_value, second_value)
      error("unification failure as " .. v .. " field value doesn't match")
    end
  end

  if prefer_left then
    return first_value
  elseif prefer_right then
    return second_value
  else
    -- create new value
    local first_type = getmetatable(first_value)
    local cons = first_type
    if variant then
      cons = first_type[variant]
    end
    local unified = cons(table.unpack(unified_args))
    return unified
  end
end

local unifier = {
  record = function(t, info)
    t.__index = t.__index or {}
    function t.__index:unify(second_value)
      return unify(self, info.params, nil, second_value)
    end
  end,
  enum = function(t, info)
    t.__index = t.__index or {}
    function t.__index:unify(second_value)
      local vname = string.sub(self.kind, #info.name + 2, -1)
      return unify(self, info.variants[vname].info.params, vname, second_value)
    end
  end,
}

value:derive(unifier)
result_info:derive(unifier)
]]

local eq = {
  record = function(t, info)
    local checks = {}
    for i, param in ipairs(info.params) do
      checks[i] = string.format("left[%q] == right[%q]", param, param)
    end
    local all_checks = table.concat(checks, " and ")
    local chunk = "return function(left, right) return " .. all_checks .. " end"
    print("record chunk: ", info.kind)
    print("###")
    print(chunk)
    print("###")
    local compiled, message = load(chunk)
    assert(compiled, message)
    local eq_fn = compiled()
    t.__eq = eq_fn
  end,
  enum = function(t, info)
    local variants_checks = {}
    for n, vname in ipairs(info.variants) do
      local vkind = info.name .. "_" .. vname
      local vdata = info.variants[vname]
      local vtype = vdata.type
      local vinfo = vdata.info
      local all_checks
      if vtype == "record" then
        local checks = {}
        for i, param in ipairs(vinfo.params) do
            checks[i] = string.format("left[%q] == right[%q]", param, param)
        end
        all_checks = table.concat(checks, " and ")
      elseif vtype == "unit" then
        all_checks = "true"
      else
        error("unknown variant type: " .. vtype)
      end
      local entry = string.format("[%q] = function(left, right) return %s end", vkind, all_checks)
      variants_checks[n] = entry
    end
    local all_variants_checks = "{\n  " .. table.concat(variants_checks, ",\n  ") .. "\n}"
    local define_all_variants_checks = "local all_variants_checks = " .. all_variants_checks

    local kind_check_expression = "left.kind == right.kind"
    local variant_check_expression = "all_variants_checks[left.kind](left, right)"
    local check_expression = kind_check_expression .. " and " .. variant_check_expression
    local check_function = "function(left, right) return " .. check_expression .. " end"

    local chunk = define_all_variants_checks .. "\nreturn " .. check_function
    print("enum chunk: ", info.name)
    print("###")
    print(chunk)
    print("###")
    local compiled, message = load(chunk)
    assert(compiled, message)
    local eq_fn = compiled()
    t.__eq = eq_fn
  end,
}

value:derive(eq)

local evaluate

local function check(
    checkable_term, -- constructed from checkable_term
    typechecking_context, -- todo
    target_type) -- must be unify with target type (there is some way we can assign metavariables to make them equal)
  -- -> type of that term, a typed term

  if checkable_term.kind == "inferred" then
    local inferred_type, typed_term = infer(checkable_term.inferred_term, typechecking_context)
    unified_type = inferred_type:unify(target_type) -- can fail, will cause lua error
    return unified_type, typed_term
  elseif checkable_term.kind == "checked_lambda" then
    -- assert that target_type is a pi type
    -- TODO open says work on other things first they will be easier
  end

  error("unknown kind in check: " .. checkable_term.kind)
end

local function infer(
    inferrable_term, -- constructed from inferrable
    typechecking_context -- todo
    )
  -- -> type of term, usage counts, a typed term,

  --print("inferring!")
  --p(inferrable_term)
  -- TODO: typecheck inferrable_term and typechecking_context?
  local usage_array = array(gen.builtin_number)
  if inferrable_term.kind == "inferrable_bound_variable" then
    local index = inferrable_term.index
    local typeof_bound = typechecking_context:get_type(index)
    local usage_counts = usage_array()
    local context_size = #typechecking_context
    for i = 1, context_size do usage_counts:append(0) end
    usage_counts[index] = 1
    local bound = typed_term.bound_variable(index)
    return typeof_bound, usage_counts, bound
  elseif inferrable_term.kind == "inferrable_typed" then
    return inferrable_term.type, inferrable_term.usage_counts, inferrable_term.typed_term
  elseif inferrable_term.kind == "inferrable_annotated_lambda" then
    local _, _, param_term = infer(inferrable_term.parameter_annotation, typechecking_context)
    --print("infer, handing off to evaluate")
    --p(param_term)
    --print("let's go")
    local eval_param_term = evaluate(param_term, typechecking_context:get_runtime_context())
    -- TODO: also handle neutral values, for inference of qtype
    if eval_param_term.kind ~= "value_qtype" then
      p(eval_param_term)
      error("lambda annotation without quantity information")
    end
    local param_quantity = eval_param_term.quantity.quantity.kind
    local inner_context = typechecking_context:append("", eval_param_term.type)
    local body_type, body_usages, body_term = infer(inferrable_term.body, inner_context)
    local result_type = value.closure(typed_term.literal(body_type), runtime_context()) -- TODO: replace free_placeholder variables with bound variables
    --p("A!")
    --p(body_usages)
    local body_usages_param = body_usages:pop_back()
    --p(body_usages)
    --p("B!")
    if param_quantity == "quantity_erased" then
      if body_usages_param > 0 then
        error("trying to use an erased parameter")
      end
    elseif param_quantity == "quantity_linear" then
      if body_usages_param > 1 then
        error("trying to use a linear parameter multiple times")
      end
    elseif param_quantity == "quantity_unrestricted" then
      -- nwn
    else
      error("unknown quantity")
    end
    local lambda_type = value.pi(
      eval_param_term,
      value.param_info(value.visibility(visibility.explicit)),
      result_type,
      value.result_info(result_info(purity.pure))
    )
    local lambda_term = typed_term.lambda(body_term)
    return lambda_type, body_usages, lambda_term
  elseif inferrable_term.kind == "inferrable_qtype" then
    local quantity_type, quantity_usages, quantity_term = infer(inferrable_term.quantity, typechecking_context)
    local type_type, type_usages, type_term = infer(inferrable_term.type, typechecking_context)
    for i, n in ipairs(type_usages) do
      local qu = quantity_usages[i] or 0
      qu = qu + n
      quantity_usages[i] = qu
    end
    local qtype = typed_term.qtype(quantity_term, type_term)
    local qtype_type = value.qtype_type(0) -- TODO: get level from the inner type
    return qtype_type, quantity_usages, qtype
  elseif inferrable_term.kind == "inferrable_pi" then
    error("nyi")
    local param_type_type, param_type_usages, param_type_term = infer(inferrable_term.param_type, typechecking_context)
    local param_info_type, param_info_usages, param_type_term = infer(inferrable_term.param_type, typechecking_context)
    local param_type_type, param_type_usages, param_type_term = infer(inferrable_term.param_type, typechecking_context)
    local param_type_type, param_type_usages, param_type_term = infer(inferrable_term.param_type, typechecking_context)
  elseif inferrable_term.kind == "inferrable_application" then
    local f_type, f_usages, f_term = infer(inferrable_term.f, typechecking_context)
    local arg_type, arg_usages, arg_term = infer(inferrable_term.arg, typechecking_context)
    if f_type.kind ~= "value_pi" then
      error("trying to apply to something whose type isn't a function type")
    elseif f_type.param_info.visibility.visibility.kind ~= "visibility_explicit" then
      error("nyi implicit parameters")
    end
    if f_type.param_type ~= arg_type then
      p(f_type)
      p(arg_type)
      error("mismatch in arg type and param type of application")
    end
    local result_type = typed_term.application(typed_term.literal(f_type.result_type), arg_term)
    --print("infer, handing off to evaluate (2)")
    --p(f_type)
    --p(result_type)
    --print("let's go")
    local eval_result_type = evaluate(result_type, typechecking_context:get_runtime_context())
    for i, n in ipairs(arg_usages) do
      local fu = f_usages[i] or 0
      fu = fu + n
      f_usages[i] = fu
    end
    local application = typed_term.application(f_term, arg_term)
    return eval_result_type, f_usages, application
  end

  --[[
  if inferrable_term.kind == "inferrable_level0" then
    return value.level_type, typed_term.level0
  elseif inferrable_term.kind == "inferrable_level_suc" then
    local arg_type, arg_term = infer(inferrable_term.previous_level, typechecking_context)
    arg_type:unify(value.level_type)
    return value.level_type, typed_term.level_suc(arg_term)
  elseif inferrable_term.kind == "inferrable_level_max" then
    local arg_type_a, arg_term_a = infer(inferrable_term.level_a, typechecking_context)
    local arg_type_b, arg_term_b = infer(inferrable_term.level_b, typechecking_context)
    arg_type_a:unify(value.level_type)
    arg_type_b:unify(value.level_type)
    return value.level_type, typed_term.level_max(arg_term_a, arg_term_b)
  elseif inferrable_term.kind == "inferrable_level_type" then
    return value.star(0), typed_term.level_type
  elseif inferrable_term.kind == "inferrable_star" then
    return value.star(1), typed_term.star(0)
  elseif inferrable_term.kind == "inferrable_prop" then
    return value.star(1), typed_term.prop(0)
  elseif inferrable_term.kind == "inferrable_prim" then
    return value.star(1), typed_term.prim
  end
  ]]

  error("unknown kind in infer: " .. inferrable_term.kind)
end

function evaluate(
    typed_term,
    runtime_context
    )
  -- -> a value

  --print("evaluating!")
  --p(typed_term)
  -- TODO: typecheck typed_term and runtime_context?
  if typed_term.kind == "typed_bound_variable" then
    return runtime_context:get(typed_term.index)
  elseif typed_term.kind == "typed_literal" then
    return typed_term.literal_value
  elseif typed_term.kind == "typed_lambda" then
    local value = value.closure(typed_term.body, runtime_context)
    return value
  elseif typed_term.kind == "typed_qtype" then
    local eval_quantity = evaluate(typed_term.quantity, runtime_context)
    local eval_type = evaluate(typed_term.type, runtime_context)
    return value.qtype(eval_quantity, eval_type)
  elseif typed_term.kind == "typed_pi" then
    local eval_param_type = evaluate(typed_term.param_type, runtime_context)
    local eval_param_info = evaluate(typed_term.param_info, runtime_context)
    local eval_result_type = evaluate(typed_term.result_type, runtime_context)
    local eval_result_info = evaluate(typed_term.result_info, runtime_context)
    return value.pi(eval_param_type, eval_param_info, eval_result_type, eval_result_info)
  elseif typed_term.kind == "typed_application" then
    local eval_f = evaluate(typed_term.f, runtime_context)
    local eval_arg = evaluate(typed_term.arg, runtime_context)
    if eval_f.kind == "value_closure" then
      local inner_context = eval_f.capture:append(eval_arg)
      return evaluate(eval_f.code, inner_context)
    elseif eval_f.kind == "value_neutral" then
      return value.neutral(neutral_value.application_stuck(eval_f.neutral_value, eval_arg))
    else
      p(eval_f)
      error("trying to apply on something that isn't a function/closure")
    end

  elseif typed_term.kind == "typed_level0" then
    return value.level(0)
  elseif typed_term.kind == "typed_level_suc" then
    local previous_level = evaluate(typed_term.previous_level, runtime_context)
    if previous_level.kind ~= "value_level" then
      p(previous_level)
      error("wrong type for previous_level")
    end
    if previous_level.level > 10 then
      error("NYI: level too high for typed_level_suc" .. tostring(previous_level.level))
    end
    return value.level(previous_level.level + 1)
  elseif typed_term.kind == "typed_level_max" then
    local level_a = evaluate(typed_term.level_a, runtime_context)
    local level_b = evaluate(typed_term.level_b, runtime_context)
    if level_a.kind ~= "value_level" or level_b.kind ~= "value_level" then
      error("wrong type for level_a or level_b")
    end
    return value.level(math.max(level_a.level, level_b.level))
  elseif typed_term.kind == "typed_level_type" then
    return value.level_type
  elseif typed_term.kind == "typed_star" then
    return value.star(typed_term.level)
  elseif typed_term.kind == "typed_prop" then
    return value.prop(typed_term.level)
  elseif typed_term.kind == "typed_prim" then
    return value.prim
  end

  error("unknown kind in evaluate " .. typed_term.kind)
end

return {
  check = check,
  infer = infer,
  evaluate = evaluate,
}
