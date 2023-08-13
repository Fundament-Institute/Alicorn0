-- provide ways to construct all terms
-- checker untyped term and typechecking context -> typed term
-- evaluator takes typed term and runtime context -> value

-- type checker monad
-- error handling and metavariable unification facilities
--
-- typechecker is allowed to fail, typechecker monad carries failures upwards
--   for now fail fast, but design should vaguely support multiple failures

-- metavariable unification
--   a metavariable is like a variable butmore meta
--   create a set of variables -> feed into code -> evaluate with respect to them
--   in order for the values produced by these two invocations to be the same, what would the metavariales need to be bound to?
--   (this is like symbolic execution)
--
-- in the typechecking monad we create a metavariable which takes a type and produces a term or value of that type and
-- we can unfy two values against each other to solve their metavariables or it can fail
-- for now unification with equality is the only kind of constraint. eventuall may be others but that's hard/no need right now

-- we will use lua errors for handling here - use if, error not assert so JIT understands
-- metavariables = table, edit the table, this is the stateful bit the monad has
-- methods on metavariable that bind equal to some value, if it is already bound it has to unify which can fail, failure cascades
-- thing passed to bind equl method on metavariable is a 'value' - enumerated datatype, like term but less cases
--   scaffolding - need to add cases here foreach new value variant
--
-- create metavariable, pass in as arg to lambda, get back result, unify against another type
--   it's ok if a metavariable never gets constrained during part of typechecking

-- checkable terms need a target type to typecheck against
local checkable = {
  inferred = function(inferred_term)
    return {
      kind = "inferred",
      inferred_term = inferred_term,
    }
  end,
  lambda = function(body) -- body is a checkable term
    return {
      kind = "checkable_lambda",
      body = body,
    }
  end,
}
-- inferrable terms can have their type inferred / don't need a target type
local inferrable = {
  level_type = {
    kind = "inferrable_level_type",
  },
  level0 = {
    kind = "inferrable_level0",
  },
  level_suc = function(previous_level) -- inferrable term
    return {
      kind = "inferrable_level_suc",
      previous_level = previous_level,
    }
  end,
  level_max = function(level_a, level_b) -- inferrable terms
    return {
      kind = "inferrable_level_max",
      level_a = level_a,
      level_b = level_b,
    }
  end
}
-- typed terms have been typechecked but do not store their type internally
local typed = {
  lambda = function(body)
    return {
      kind = "typed_lambda",
      body = body,
    }
  end,
  level_type = {
    kind = "inferrable_level_type",
  },
  level0 = {
    kind = "typed_level0",
  },
  level_suc = function(previous_level) -- typed term
    return {
      kind = "typed_level_suc",
      previous_level = previous_level,
    }
  end,
  level_max = function(level_a, level_b) -- inferrable terms
    return {
      kind = "typed_level_max",
      level_a = level_a,
      level_b = level_b,
    }
  end
}
local values = {
  pi = function(
      argtype,
      arginfo,
      restype,
      resinfo)
    return {
      kind = "pi",
      argtype = argtype,
      arginfo = arginfo,
      restype = restype,
      resinfo = resinfo,
    }
  end,
  -- closure is a type that contains a typed term corresponding to the body
  -- and a runtime context representng the bound context where the closure was created
  closure = function(),
      -- TODO
  end
  level_type = {
    kind = "value_level_type",
  },
  level = function(level), -- the level number
      return {
        kind = "value_level",
        level = level,
      }
  end,
  star = function(level), -- the level number
      return {
        kind = "star",
        level = level,
      }
  end,
}

local function unify(
    first_value,
    second_value)
  -- -> unified value,
end

local function check(
    checkable_term, -- constructed from checkable
    typechecking_context, -- todo
    target_type) -- must be unify with target type (there is some way we can assign metavariables to make them equal)
  -- -> type of that term, a typed term

  if checkable_term.kind == "inferred" then
    local inferred_type, typed_term = infer(checkable_term.inferred_term, typechecking_context)
    unified_type = unify(inferred_type, target_type) -- can fail, will cause lua error
    return unified_type, typed_term
  elseif checkable_term.kind == "checked_lambda" then
    -- assert that target_type is a pi type
    -- TODO open says work on other things first they will be easier
  end


end

local function infer(
    inferrable_term, -- constructed from inferrable
    typechecking_context, -- todo
    )
  -- -> type of term, a typed term,
  if inferrable_term.kind = "inferrable_level0" then
    return values.level_type, typed.level0
  elseif inferrable_term.kind = "inferrable_level_suc" then
    local arg_type, arg_term = infer(inferrable_term.previous_level, typechecking_context)
    unify(arg_type, values.level_type)
    return values.level_type, typed.level_suc(arg_term)
  elseif inferrable_term.kind = "inferrable_level_max" then
    local arg_type_a, arg_term_a = infer(inferrable_term.level_a, typechecking_context)
    local arg_type_b, arg_term_b = infer(inferrable_term.level_b, typechecking_context)
    unify(arg_type_a, values.level_type)
    unify(arg_type_b, values.level_type)
    return values.level_type, typed.level_max(arg_term_a, arg_term_b)
  elseif inferrable_term.kind = "inferrable_level_type" then
    return values.star(0), typed.level_type
  end
end

local function evaluate(
    typed_term,
    runtime_context,
    )
  -- -> a value
end

return {
  checkable = checkable, -- {}
  inferrable = inferrable, -- {}
  check = check, -- fn
  infer = infer, -- fn
  typed = typed, -- {}
  evaluate = evaluate, -- fn
  values = values, -- {}
}
