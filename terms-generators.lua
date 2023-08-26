-- record and enum are nominative types.
-- this means that two record types, given the same arguments, are distinct.
-- values constructed from one type are of a different type compared to values
-- constructed from the other.
-- (likewise for enum)

-- foreign, map, and array are structural types.
-- this means that two map types, given the same key-type and value-type, alias
-- each other.
-- values constructed from one type are, at a high level, of the same type
-- as values constructed from the other.
-- (likewise for array, and foreign given the same value_check function;
-- foreign values are constructed elsewhere)

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
    if type(param_type) ~= "table" then
      error("wrong argument passed to parameter type in constructor " .. kind .. ", parameter " .. v " (possible typo?)")
    end
  end
end

local function gen_record(self, cons, kind, params_with_types)
  local params, params_types = parse_params_with_types(params_with_types)
  validate_params_types(kind, params, params_types)
  setmetatable(cons, {
    __call = function(cons, ...)
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

local map_type_mt = {
  __call = function(self)
    local val = {
      __map = {},
    }
    setmetatable(val, self)
    return val
  end,
  __eq = function(left, right)
    return left.key_type == right.key_type and left.value_type == right.value_type
  end,
}

local map_methods = {
  pairs = function(self)
    return pairs(self.__map)
  end,
}

local function gen_map_fns(key_type, value_type)
  local function index(self, key)
    local method = map_methods[key]
    if method then
      return method
    end
    if key_type.value_check(key) ~= true then
      p("map-index", key_type, value_type)
      p(key)
      error("wrong key type passed to indexing")
    end
    return self.__map[key]
  end
  local function newindex(self, key, value)
    local method = map_methods[key]
    if method then
      p(method)
      error("attempted index-assignment that shadows a method")
    end
    if key_type.value_check(key) ~= true then
      p("map-index-assign", key_type, value_type)
      p(key)
      error("wrong key type passed to index-assignment")
    end
    if value_type.value_check(value) ~= true then
      p("map-index-assign", key_type, value_type)
      p(value)
      error("wrong value type passed to index-assignment")
    end
    self.__map[key] = value
  end
  return index, newindex
end

-- TODO: memoize? otherwise LOTS of tables will be constructed,
-- through repeated calls to declare_map
local function define_map(self, key_type, value_type)
  setmetatable(self, map_type_mt)
  self.key_type = key_type
  self.value_type = value_type
  self.__index, self.__newindex = gen_map_fns(key_type, value_type)
  -- NOTE: this isn't primitive equality; this type has a __eq metamethod!
  self.value_check = metatable_equality(self)
  return self
end

local array_type_mt = {
  __call = function(self, ...)
    local args = { ... }
    local val = {
      n = #args,
      array = args,
    }
    setmetatable(val, self)
    return val
  end,
  __eq = function(left, right)
    return left.value_type == right.value_type
  end,
}

local array_methods = {
  ipairs = function(self)
    local function iter(state, ctl)
      local i = state[1]
      state[1] = i + 1
      if i >= self.n then
        return
      else
        return i, self.array[i]
      end
    end
    return iter, {0}
  end,
  len = function(self)
    return self.n
  end,
  append = function(self, val)
    self[self.n] = val
  end,
}

local function gen_array_fns(value_type)
  local function index(self, key)
    local method = array_methods[key]
    if method then
      return method
    end
    if type(key) ~= "number" then
      p("array-index", value_type)
      p(key)
      error("wrong key type passed to indexing")
    end
    -- check if integer
    -- there are many nice ways to do this in lua >=5.3
    -- unfortunately, this is not us
    if math.floor(key) ~= key then
      p(key)
      error("key passed to indexing is not an integer")
    end
    if key < 0 or key >= self.n then
      p(key, self.n)
      error("key passed to indexing is out of bounds")
    end
    return self.array[key]
  end
  local function newindex(self, key, value)
    if type(key) ~= "number" then
      p("array-index", value_type)
      p(key)
      error("wrong key type passed to index-assignment")
    end
    if math.floor(key) ~= key then
      p(key)
      error("key passed to index-assignment is not an integer")
    end
    -- equal can be used to append
    if key < 0 or key > self.n then
      p(key, self.n)
      error("key passed to index-assignment is out of bounds")
    end
    if value_type.value_check(value) ~= true then
      p("map-index-assign", key_type, value_type)
      p(value)
      error("wrong value type passed to index-assignment")
    end
    self.array[key] = value
    self.n = self.n + 1
  end
  return index, newindex
end

-- TODO: see define_map
local function define_array(self, value_type)
  setmetatable(self, array_type_mt)
  self.value_type = value_type
  self.__index, self.__newindex = gen_array_fns(value_type)
  -- NOTE: this isn't primitive equality; this type has a __eq metamethod!
  self.value_check = metatable_equality(self)
  return self
end

local type_mt = {
  __index = {
    define_record = define_record,
    define_enum = define_enum,
    define_foreign = define_foreign,
    define_map = define_map,
    define_array = define_array,
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
  declare_map = new_self(define_map),
  declare_array = new_self(define_array),
  declare_type = new_self(define_type),
  metatable_equality = metatable_equality,
  builtin_number = gen_builtin("number"),
  builtin_string = gen_builtin("string"),
}
