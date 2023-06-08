local types = require 'basic-types'
local utils = require 'utils'

-- Nothing outside the definition of the IR should have access to these tokens.
local tokens = {
  -- category ops for func
  identity = {}, -- func(a, a)
  compose = {}, -- tuple(func(a, b), func(b, c)) -> func(a, c)

  -- avoid using the typical closed cartesian category operations and instead buld a set which both makes tuples form a monoid and is friendlier to linear values
  --tuplespread = {}, -- tuple(func(a, b), func(a, c), ...) -> func(a, tuple(b, c, ...))
  --tupleextract = {}, -- n -> func(tuple(...), nth item of the tuple)
  --tupleconcat = {}, -- tuple(tuple(a, ...), tuple(b, ...), ...) -> tuple(a, ..., b, ..., ...)
  tuplelift = {}, -- func(a, tuple(a))
  tupleunlift = {}, -- func(tuple(a), a)
  tuplefork = {}, -- tuple(func(a, b), func(c, d), ...) -> func(tuple..(a, c, ...), tuple..(b, d, ...))
  tuplepermute = {}, -- permutation -> func(a, b) where b is the specified permutation of the tuple a
  duplicate = {}, -- func(a, tuple..(a, a))

  -- terminal object, used to implement drop
  discard = {}, -- func(a, unit)

  -- closed category
  apply = {}, -- func(tuple((a -> b), a), b)
  curry = {}, -- func(tuple(a, b), c) -> func(a, b -> c)
  uncurry = {}, -- func(a, (b -> c)) -> func(tuple(a, b), c)

  -- introduce a constant
  unitArrow = {}, -- func(unit, b)

  -- let binop = lambda(a) func(tuple(a, a), tuple(a))
  -- let func1 =
  -- boolean ops category
  notC = {}, -- func1(bool, bool)
  andC = {}, -- func(tuple(bool, bool), tuple(bool))
  orC = {}, -- binop(bool)
  ifC = {}, -- tuple(func(tuple..(tuple(witnesseq(c, true)), a), b), func(tuple..(tuple(witnesseq(c, true)), a), b) -> func(tuple..(tuple(bool), .. a), b)

  negC = {}, -- func1(a, a)
  addC = {}, -- binop(a)
  subC = {}, -- binop(a)
  mulC = {}, -- binop(a)
  divC = {}, -- binop(a)

  -- enuminject = {}, -- (n : uint) -> func(alternatives[n], enum(alternatives))
  -- enummatch = {}, -- tuple(func(alternatives[1], b), func(alternatives[2], b), ...) -> func(enum(alternatives), b)

  -- enums are the duals of tuples
  enumlift = {}, -- func(a, enum(a))
  enumunlift = {}, -- func(enum(a), a)
  enumfork = {}, -- tuple(func(a, b), func(c, d), ...) -> func(enum..(a, c, ...), enum..(b, d, ...))
  enumpermute = {}, -- permutation -> func(a, b) where b is the specified permtation of the enum a
  merge = {}, -- func(enum..(a, a), a)

  hallucinate = {}, -- func(void, b) ; the categorical dual of discard

  distenumtuple = {}, -- given an enum that has each element as a tuple with the same start, convert into a tuple of the common prefix with an enum of the remaining elements
  -- func(enum(a...), tuple(b, enum(c...))) where each a is tuple(b, c)
  disttupleenum = {}, -- given a tuple that has as its suffix an enum, convert into an enum that has as each elementa tuple a prefix of the outer tuple and a suffix of the enum element
  -- func(tuple(a, enum(b...)), enum(c...)) where each c is tuple(a, b)

  wrap = {} -- func(a, b) -> func(a, c) where c is stored as b
  unwrap = {} -- func(a, b) -> func(a, c) where b is stored as c
}
-- operator implementations are functions of the signature
-- (type_parameters, bound_data, compiledinputs) -> compiledresult
-- These act as modular components to fold an algebra with the carrier
-- (operator, type parameters for operator, bound data for operator, compiled inputs to operator)
-- so that it can fold to a single compiled output.

local function basic_component(name, symbols)
  return function(definition)
    local component = {handlers = {}, name = name}
    for k, v in pairs(symbols) do
      if definition[k] then
        component.handlers[v] = definition[k]
      else
        error("implementation for " .. name .. " is missing definition for " .. k)
      end
    end
    return component
  end
end

local function genbuilder(token, typechecker)
  return function(type_parameters, bound_data, inputs)
    local input_types = {}
    for i, v in ipairs(inputs) do
      input_types[i] = v.type
    end
    local type = typechecker(type_parameters, bound_data, input_types)
    if not type then error "typechecker didn't produce a type" end
    return {
      operator = token,
      type_parameters = type_parameters,
      bound_data = bound_data,
      inputs = inputs,
      type = type
    }
  end
end


local components = {
  category = basic_component("category", {identity = tokens.identity, compose = tokens.compose}),
  tuples = basic_component("tuples", {
    lift = tokens.tuplelift,
    unlift = tokens.tupleunlift,
    fork = tokens.tuplefork,
    permute = tokens.tuplepermute,
    duplicate = tokens.duplicate
  }),
  discard = basic_component("discard", {discard = tokens.discard}),
  closed = basic_component("closed", {apply = tokens.apply, curry = tokens.curry, uncurry = tokens.uncurry})
}

--TODO: write generic component tool.

return {
  enums = component "enums"
  {
    lift = {
      typechecker = function(type_parameters, bound_data, input_types)
        return types.fn(type_parameters[1], types.enum{type_parameters[1]})
      end,
      constructor = function(type)
        return {type}, {}, {}
      end
    },
    unlift = {
      typechecker = function(type_parameters, bound_data, input_types)
        return types.fn(types.enum{type_parameters[1]}, type_parameters[1])
      end,
      constructor = function(type)
        return {type}, {}, {}
      end
    },
    fork = {
      typechecker = function(type_parameters, bound_data, input_types)
        local paramvariants, resultvariants = {}, {}
        for i, v in ipairs(input_types) do
          if v.kind == types.fn then
            local param, result = v.args[1], v.args[2]
            if param.kind == types.enum and result.kind == types.enum then
              paramvariants = utils.concat(paramvariants, param.args[1])
              resultvariants = utils.concat(resultvariants, result.args[1])
            else
              error "both param and result of every component of a fork must be an enum"
            end
          else
            error "every component of a fork must be a function"
          end
        end
        return types.fn(types.enum(paramvariants), types.enum(resultvariants))
      end,
      constructor = function(...)
        return {}, {}, {...}
      end
    },
    permute = {
      typechecker = function(type_parameters, bound_data, input_types)
        error "nyi"
      end
    }
  }
}
