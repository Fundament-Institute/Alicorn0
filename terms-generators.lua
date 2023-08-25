local function new_self(fn)
  return function(...)
    return fn({}, ...)
  end
end

local function metatable_equality(mt)
  return function(val)
    return getmetatable(val) == mt
  end
end

local function parse_params_with_types(params_with_types)
  -- params are odd entries of params_with_types
  -- params_types are even
  local params = {}
  local params_types = {}
  for i, v in ipairs(params_with_types) do
    if i % 2 == 1 then
      params[math.floor(i / 2 + 1)] = v
    else
      params_types[math.floor(i / 2)] = v
    end
  end
  return params, params_types
end

local function validate_params_types(kind, params, params_types)
  -- ensure there are at least as many param types as there are params
  for i, v in ipairs(params) do
    local param_type = params_types[i]
    if not param_type then
      error("nil passed to parameter type in constructor " .. kind .. ", parameter " .. v " (probable typo?)")
    end
  end
end

local function gen_record(self, cons, kind, params_with_types)
  local params, params_types = parse_params_with_types(params_with_types)
  validate_params_types(kind, params, params_types)
  setmetatable(cons, {
    __call = function(_self, ...)
      local args = { ... }
      local val = {
        kind = kind,
      }
      for i, v in ipairs(params) do
        local argi = args[i]
        -- type-check constructor arguments
        if params_types[i].value_check(argi) ~= true then
          p(argi)
          error("wrong argument type passed to constructor " .. kind .. ", parameter " .. v)
        end
        val[v] = argi
      end
      setmetatable(val, self)
      return val
    end,
  })
  local derive_info = {
    kind = kind,
    params = params,
    params_types = params_types,
  }
  return cons, derive_info
end

local function define_record(self, kind, params_with_types)
  local self, derive_info = gen_record(self, self, kind, params_with_types)
  function self:derive(deriver)
    return deriver.record(self, derive_info)
  end
  self.value_check = metatable_equality(self)
  return self
end

local function gen_unit(self, kind)
  local val = {
    kind = kind,
  }
  local derive_info = {
    kind = kind,
    params = {},
    params_types = {},
  }
  setmetatable(val, self)
  return val, derive_info
end

local function define_enum(self, name, variants)
  setmetatable(self, nil)
  local derive_variants = {}
  for i, v in ipairs(variants) do
    local vname = v[1]
    local vparams_with_types = v[2]
    local kind = name .. "_" .. vname
    derive_variants[i] = vname
    if vparams_with_types then
      local record_cons, record_info = gen_record(self, {}, kind, vparams_with_types)
      self[vname] = record_cons
      derive_variants[vname] = {
        type = "record",
        info = record_info,
      }
    else
      local unit_val, unit_info = gen_unit(self, kind)
      self[vname] = unit_val
      derive_variants[vname] = {
        type = "unit",
        info = unit_info,
      }
    end
  end
  local derive_info = {
    name = name,
    variants = derive_variants,
  }
  function self:derive(deriver)
    return deriver.enum(self, derive_info)
  end
  self.value_check = metatable_equality(self)
  return self
end

local function define_foreign(self, value_check)
  setmetatable(self, nil)
  self.value_check = value_check
  return self
end

local type_mt = {
  __index = {
    define_record = define_record,
    define_enum = define_enum,
    define_foreign = define_foreign,
  }
}

local function define_type(self)
  setmetatable(self, type_mt)
  return self
end

local function gen_builtin(typename)
  return define_foreign({}, function(val)
    return type(val) == typename
  end)
end

return {
  declare_record = new_self(define_record),
  declare_enum = new_self(define_enum),
  declare_foreign = new_self(define_foreign),
  declare_type = new_self(define_type),
  metatable_equality = metatable_equality,
  builtin_number = gen_builtin("number"),
  builtin_string = gen_builtin("string"),
}
