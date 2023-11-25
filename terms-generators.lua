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

---@class Type
---@field value_check ValueCheckFn
---@alias ValueCheckFn fun(val: Type): boolean

---@class Value
---@field kind string

-- TODO: are generic annotations powerful enough to describe this function?
-- worked around at the bottom of this file
local function new_self(fn)
	return function(...)
		return fn({}, ...)
	end
end

---@param mt table
---@return ValueCheckFn
local function metatable_equality(mt)
	if type(mt) ~= "table" then
		error("trying to define metatable equality to something that isn't a metatable (possible typo?)")
	end
	return function(val)
		return getmetatable(val) == mt
	end
end

---@param params_with_types (string | Type)[]
---@return string[] params
---@return Type[] params_types
local function parse_params_with_types(params_with_types)
	-- params are odd entries of params_with_types
	-- params_types are even
	local params = {}
	local params_types = {}
	local odd = true
	local i = 1
	for _, v in ipairs(params_with_types) do
		if odd then
			params[i] = v
		else
			params_types[i] = v
			i = i + 1
		end
		odd = not odd
	end
	return params, params_types
end

---@param kind string
---@param params string[]
---@param params_types Type[]
---@return nil
local function validate_params_types(kind, params, params_types)
	-- ensure there are at least as many param types as there are params
	-- also ensure there is at least one param
	local at_least_one = false
	for i, v in ipairs(params) do
		at_least_one = true
		local param_type = params_types[i]
		if type(param_type) ~= "table" or type(param_type.value_check) ~= "function" then
			error(
				"trying to set a parameter type to something that isn't a type, in constructor "
					.. kind
					.. ", parameter "
					.. v
					.. " (possible typo?)"
			)
		end
	end
	if not at_least_one then
		error("trying to make a record type, or a record variant of an enum type, with no parameters")
	end
end

-- TODO: cons turns from a table to a callable table. how to conveniently annotate this?
---@param self table
---@param cons table
---@param kind string
---@param params_with_types (string | Type)[]
---@return table cons
---@return RecordDeriveInfo derive_info
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
					error("wrong argument type passed to constructor " .. kind .. ", parameter '" .. v .. "'")
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

---@class Record: Type
---@field derive fun(self: Record, deriver: Deriver)

---@param self table
---@param kind string
---@param params_with_types (string | Type)[]
---@return Record self
local function define_record(self, kind, params_with_types)
	local self, derive_info = gen_record(self, self, kind, params_with_types)
	function self:derive(deriver)
		return deriver.record(self, derive_info)
	end
	self.value_check = metatable_equality(self)
	return self
end

---@param self table
---@param kind string
---@return Value val
---@return UnitDeriveInfo derive_info
local function gen_unit(self, kind)
	local val = {
		kind = kind,
	}
	local derive_info = {
		kind = kind,
	}
	setmetatable(val, self)
	return val, derive_info
end

---@class Enum: Type
---@field derive fun(self: Enum, deriver: Deriver)

---@param self table
---@param name string
---@param variants { [1]: string, [2]: (string | Type)[] }[]
---@return Enum self
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

---@class Foreign: Type

---@param self table
---@param value_check ValueCheckFn
---@return Foreign self
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
	pretty_print = function(self, prefix)
		local np = prefix .. " "
		local parts = {}
		local i = 1
		for k, v in pairs(self.__map) do
			local function pp(x, p)
				return ((type(x) == "table" and x.pretty_print) or tostring)(x, p)
			end
			parts[i] = string.format("%s = %s", pp(k, prefix), pp(v, np))
			i = i + 1
		end
		return string.format("[\n" .. np .. "%s\n" .. prefix .. "]", table.concat(parts, ",\n" .. np))
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

---@class Map: Type

-- TODO: memoize? otherwise LOTS of tables will be constructed,
-- through repeated calls to declare_map
---@param self table
---@param key_type Type
---@param value_type Type
---@return Map self
local function define_map(self, key_type, value_type)
	if
		type(key_type) ~= "table"
		or type(key_type.value_check) ~= "function"
		or type(value_type) ~= "table"
		or type(value_type.value_check) ~= "function"
	then
		error("trying to set the key or value type to something that isn't a type (possible typo?)")
	end
	setmetatable(self, map_type_mt)
	self.key_type = key_type
	self.value_type = value_type
	self.__index, self.__newindex = gen_map_fns(key_type, value_type)
	self.__pairs = map_methods.pairs
	-- NOTE: this isn't primitive equality; this type has a __eq metamethod!
	self.value_check = metatable_equality(self)
	return self
end

local array_type_mt = {
	__call = function(self, ...)
		local val = {
			n = 0,
			array = {},
		}
		setmetatable(val, self)
		local args = { ... }
		for i = 1, select("#", ...) do
			val:append(args[i])
		end
		return val
	end,
	__eq = function(left, right)
		return left.value_type == right.value_type
	end,
}

local array_methods = {
	ipairs = function(self)
		return ipairs(self.array)
	end,
	len = function(self)
		return self.n
	end,
	append = function(self, val)
		self[self.n + 1] = val
	end,
	copy = function(self, first, last)
		local first = first or 1
		local last = last or #self
		local mt = getmetatable(self)
		local new = mt()
		for i = first, last do
			new:append(self.array[i])
		end
		return new
	end,
	unpack = function(self)
		return table.unpack(self.array)
	end,
	pretty_print = function(self, prefix)
		local parts = {}
		for i, v in ipairs(self.array) do
			parts[i] = ((type(v) == "table" and v.pretty_print) or tostring)(v, prefix)
		end
		return string.format("[%s]", table.concat(parts, ", "))
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
			error("wrong key type passed to indexing: " .. key)
		end
		-- check if integer
		-- there are many nice ways to do this in lua >=5.3
		-- unfortunately, this is not us
		if math.floor(key) ~= key then
			p(key)
			error("key passed to indexing is not an integer")
		end
		if key < 1 or key > self.n then
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
		-- n+1 can be used to append
		if key < 1 or key > self.n + 1 then
			p(key, self.n)
			error("key passed to index-assignment is out of bounds")
		end
		if value_type.value_check(value) ~= true then
			p("array-index-assign", value_type)
			p(value)
			error("wrong value type passed to index-assignment")
		end
		self.array[key] = value
		if key > self.n then
			self.n = key
		end
	end
	return index, newindex
end

---@class Array: Type

-- TODO: see define_map
---@param self table
---@param value_type Type
---@return Array self
local function define_array(self, value_type)
	if type(value_type) ~= "table" or type(value_type.value_check) ~= "function" then
		error("trying to set the value type to something that isn't a type (possible typo?)")
	end
	setmetatable(self, array_type_mt)
	self.value_type = value_type
	self.__index, self.__newindex = gen_array_fns(value_type)
	self.__ipairs = array_methods.ipairs
	self.__len = array_methods.len
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
	},
}

---@type ValueCheckFn
local function undefined_value_check(val)
	error("trying to typecheck a value against a type that has been declared but not defined")
end

---@param self table
---@return Type self
local function define_type(self)
	setmetatable(self, type_mt)
	self.value_check = undefined_value_check
	return self
end

---@param typename string
---@return Foreign
local function gen_builtin(typename)
	return define_foreign({}, function(val)
		return type(val) == typename
	end)
end

return {
	---@type fun(kind: string, params_with_types: (string | Type)[]): Record
	declare_record = new_self(define_record),
	---@type fun(name: string, variants: { [1]: string, [2]: (string | Type)[] }): Enum
	declare_enum = new_self(define_enum),
	-- Make sure the function you pass to this returns true, not just a truthy value
	---@type fun(value_check: ValueCheckFn): Foreign
	declare_foreign = new_self(define_foreign),
	---@type fun(key_type: Type, value_type: Type): Map
	declare_map = new_self(define_map),
	---@type fun(value_type: Type): Array
	declare_array = new_self(define_array),
	---@type fun(): Type
	declare_type = new_self(define_type),
	metatable_equality = metatable_equality,
	builtin_number = gen_builtin("number"),
	builtin_string = gen_builtin("string"),
	any_lua_type = define_foreign({}, function()
		return true
	end),
}
