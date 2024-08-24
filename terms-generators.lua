local derivers = require "./derivers"

-- record and enum are nominative types.
-- this means that two record types, given the same arguments, are distinct.
-- values constructed from one type are of a different type compared to values
-- constructed from the other.
-- (likewise for enum)

-- foreign, map, set, and array are structural types.
-- this means that two map types, given the same key-type and value-type, alias
-- each other. values constructed from one type are of the same type as values
-- constructed from the other.
-- (likewise for set and array, and foreign given the same value_check function;
-- foreign values are constructed elsewhere)

---@alias ValueCheckFn fun(val: any): boolean

---@class Type
---@field value_check ValueCheckFn
---@field derive fun(Type, Deriver, ...)
---@field derived_value_name boolean?
---@field value_name fun(): string

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

---@alias ParamsWithTypes (string | Type)[]

---@param params_with_types ParamsWithTypes
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
	local params_set = {}
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
		if params_set[v] then
			error(
				"constructor " .. kind .. " must have unique parameter names ('" .. v .. "' was given more than once)"
			)
		end
		params_set[v] = true
	end
	if not at_least_one then
		error("constructor " .. kind .. " must take at least one parameter, or be changed to a unit")
	end
end

---@class RecordType: Type
---@field derive fun(self: RecordType, deriver: Deriver, ...)
---@field _kind string
---@field derived_eq boolean?
---@field __eq fun(left: RecordValue, right: RecordValue): boolean
---@field derived_unwrap boolean?
---@field __index table
---@field derived_pretty_print boolean?
---@field __tostring function(RecordValue): string
---@field derived_diff boolean?

---@class RecordValue: Value
---@field pretty_print fun(RecordValue, ...)
---@field default_print fun(RecordValue, ...)
---@field diff fun(RecordValue)

---@param self table
---@param cons table
---@param kind string
---@param params_with_types ParamsWithTypes
---@return RecordDeriveInfo derive_info
local function gen_record(self, cons, kind, params_with_types)
	local params, params_types = parse_params_with_types(params_with_types)
	validate_params_types(kind, params, params_types)
	setmetatable(cons, {
		__call = function(_, ...)
			local args = { ... }
			local val = {
				kind = kind,
			}
			for i, v in ipairs(params) do
				local argi = args[i]
				-- type-check constructor arguments
				if params_types[i].value_check(argi) ~= true then
					print("value of parameter " .. v .. ": (follows)")
					p(argi)
					print("expected type of parameter " .. v .. " is :", params_types[i])
					--for i = 2, 25 do
					--	local d = debug.getinfo(i, "Sln")
					--	print(string.format("%s %s %s: %s:%d", d.what, d.namewhat, d.name, d.source, d.currentline))
					--end
					error("wrong argument type passed to constructor " .. kind .. ", parameter '" .. v .. "'")
				end
				val[v] = argi
			end
			setmetatable(val, self)
			return val
		end,
	})
	---@type RecordDeriveInfo
	local derive_info = {
		kind = kind,
		params = params,
		params_types = params_types,
	}
	return derive_info
end

local function record_tostring(self)
	return "terms-gen record: " .. self._kind
end

---@param self table
---@param kind string
---@param params_with_types ParamsWithTypes
---@return RecordType self
local function define_record(self, kind, params_with_types)
	local derive_info = gen_record(self, self, kind, params_with_types)
	---@cast self RecordType
	getmetatable(self).__tostring = record_tostring
	self.value_check = metatable_equality(self)
	function self:derive(deriver, ...)
		return deriver.record(self, derive_info, ...)
	end
	self._kind = kind
	self:derive(derivers.eq)
	self:derive(derivers.unwrap)
	self:derive(derivers.diff)
	self:derive(derivers.value_name)
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
	---@type UnitDeriveInfo
	local derive_info = {
		kind = kind,
	}
	setmetatable(val, self)
	return val, derive_info
end

---@class EnumType: Type
---@field derive fun(self: EnumType, deriver: Deriver, ...)
---@field _name string
---@field derived_eq boolean?
---@field __eq fun(left: EnumValue, right: EnumValue): boolean
---@field derived_is boolean?
---@field __index table
---@field derived_unwrap boolean?
---@field derived_as boolean?
---@field derived_pretty_print boolean?
---@field __tostring function(EnumValue): string
---@field derived_diff boolean?

---@class EnumValue: Value
---@field pretty_print fun(EnumValue, ...)
---@field default_print fun(EnumValue, ...)
---@field diff fun(EnumValue)

local enum_type_mt = {
	__tostring = function(self)
		return "terms-gen enum: " .. self._name
	end,
}

---@alias Variants [ string, ParamsWithTypes ][]

---@param self table
---@param name string
---@param variants Variants
---@return EnumType self
local function define_enum(self, name, variants)
	setmetatable(self, enum_type_mt)
	---@cast self EnumType
	self.value_check = metatable_equality(self)
	local derive_variants = {}
	for i, v in ipairs(variants) do
		local vname = v[1]
		local vparams_with_types = v[2]
		local vkind = name .. "." .. vname
		if self[vname] then
			error("enum variant " .. vkind .. " is defined multiple times")
		end
		derive_variants[i] = vname
		if vparams_with_types then
			local record_cons = {}
			local record_info = gen_record(self, record_cons, vkind, vparams_with_types)
			self[vname] = record_cons
			derive_variants[vname] = {
				type = derivers.EnumDeriveInfoVariantKind.Record,
				info = record_info,
			}
		else
			local unit_val, unit_info = gen_unit(self, vkind)
			self[vname] = unit_val
			derive_variants[vname] = {
				type = derivers.EnumDeriveInfoVariantKind.Unit,
				info = unit_info,
			}
		end
	end
	---@type EnumDeriveInfo
	local derive_info = {
		name = name,
		variants = derive_variants,
	}
	function self:derive(deriver, ...)
		return deriver.enum(self, derive_info, ...)
	end
	self._name = name
	self:derive(derivers.eq)
	self:derive(derivers.is)
	self:derive(derivers.unwrap)
	self:derive(derivers.as)
	self:derive(derivers.diff)
	self:derive(derivers.value_name)
	return self
end

---@class ForeignType: Type
---@field derive fun(self: ForeignType, deriver: Deriver, ...)
---@field lsp_type string

local foreign_type_mt = {
	__tostring = function(self)
		return "terms-gen foreign: " .. self.lsp_type
	end,
}

---@param self table
---@param value_check ValueCheckFn
---@param lsp_type string
---@return ForeignType self
local function define_foreign(self, value_check, lsp_type)
	setmetatable(self, foreign_type_mt)
	---@cast self ForeignType
	self.value_check = value_check
	---@type ForeignDeriveInfo
	local derive_info = {
		value_check = value_check,
		lsp_type = lsp_type or "unknown",
	}
	function self:derive(deriver, ...)
		return deriver.foreign(self, derive_info, ...)
	end
	self.lsp_type = lsp_type
	self:derive(derivers.value_name)
	return self
end

---@class MapType: Type
---@field derive fun(self: MapType, deriver: Deriver, ...)
---@field key_type Type
---@field value_type Type
---@field __index table
---@field __newindex function
---@field __pairs function(MapValue): function, MapValue, Value?
---@field derived_pretty_print boolean?
---@field __tostring function(MapValue): string

---@class MapValue: Value
---@field _map { [Value]: Value }
---@field set fun(MapValue, Value, Value)
---@field reset fun(MapValue, Value)
---@field get fun(MapValue, Value): Value?
---@field pairs fun(MapValue): function, MapValue, Value?
---@field pretty_print fun(MapValue, ...)
---@field default_print fun(MapValue, ...)

local map_type_mt = {
	__call = function(self)
		local val = {
			_map = {},
		}
		setmetatable(val, self)
		return val
	end,
	__eq = function(left, right)
		return left.key_type == right.key_type and left.value_type == right.value_type
	end,
	__tostring = function(self)
		return "terms-gen map key:<" .. tostring(self.key_type) .. "> val:<" .. tostring(self.value_type) .. ">"
	end,
}

local function gen_map_methods(self, key_type, value_type)
	return {
		set = function(val, key, value)
			if key_type.value_check(key) ~= true then
				p("map-set", key_type, value_type)
				p(key)
				error("wrong key type passed to map:set")
			end
			if value_type.value_check(value) ~= true then
				p("map-set", key_type, value_type)
				p(value)
				error("wrong value type passed to map:set")
			end
			val._map[key] = value
		end,
		reset = function(val, key)
			if key_type.value_check(key) ~= true then
				p("map-reset", key_type, value_type)
				p(key)
				error("wrong key type passed to map:reset")
			end
			val._map[key] = nil
		end,
		get = function(val, key)
			if key_type.value_check(key) ~= true then
				p("map-get", key_type, value_type)
				p(key)
				error("wrong key type passed to map:get")
			end
			return val._map[key]
		end,
		pairs = function(val)
			return pairs(val._map)
		end,
		copy = function(val, onto)
			if not onto then
				onto = self()
			end
			local rt = getmetatable(onto)
			if self ~= rt then
				error("map:copy must be passed maps of the same type")
			end
			for k, v in val:pairs() do
				onto:set(k, v)
			end
			return onto
		end,
		union = function(left, right)
			local rt = getmetatable(right)
			if self ~= rt then
				error("map:union must be passed maps of the same type")
			end
			local new = left:copy()
			right:copy(new)
			return new
		end,
	}
end

local function map_newindex()
	error("index-assignment of maps is no longer allowed. use :set()")
end

local map_memo = {}

---@param self table
---@param key_type Type
---@param value_type Type
---@return MapType self
local function define_map(self, key_type, value_type)
	if
		type(key_type) ~= "table"
		or type(key_type.value_check) ~= "function"
		or type(value_type) ~= "table"
		or type(value_type.value_check) ~= "function"
	then
		error("trying to set the key or value type to something that isn't a type (possible typo?)")
	end

	if not map_memo[key_type] then
		map_memo[key_type] = {}
	end
	if map_memo[key_type][value_type] then
		return map_memo[key_type][value_type]
	else
		map_memo[key_type][value_type] = self
	end

	setmetatable(self, map_type_mt)
	---@cast self MapType
	-- NOTE: this isn't primitive equality; this type has a __eq metamethod!
	self.value_check = metatable_equality(self)
	---@type MapDeriveInfo
	local derive_info = {
		key_type = key_type,
		value_type = value_type,
	}
	function self:derive(deriver, ...)
		return deriver.map(self, derive_info, ...)
	end
	self.key_type = key_type
	self.value_type = value_type
	self.__index = gen_map_methods(self, key_type, value_type)
	self.__newindex = map_newindex
	self.__pairs = self.__index.pairs
	self:derive(derivers.pretty_print)
	self:derive(derivers.value_name)
	return self
end

---@class SetType: Type
---@field derive fun(self: SetType, deriver: Deriver, ...)
---@field key_type Type
---@field __index table
---@field __pairs function(SetValue): function, SetValue, Value?
---@field derived_pretty_print boolean?
---@field __tostring function(SetValue): string

---@class SetValue: Value
---@field _set { [Value]: boolean }
---@field put fun(SetValue, Value)
---@field remove fun(SetValue, Value)
---@field test fun(SetValue, Value): boolean?
---@field pairs function(SetValue): function, SetValue, Value?
---@field copy fun(SetValue, SetValue?): SetValue
---@field union fun(SetValue, SetValue): SetValue
---@field subtract fun(SetValue, SetValue): SetValue
---@field superset fun(SetValue, SetValue): boolean
---@field pretty_print fun(SetValue, ...)
---@field default_print fun(SetValue, ...)

local set_type_mt = {
	__call = function(self)
		local val = {
			_set = {},
		}
		setmetatable(val, self)
		return val
	end,
	__eq = function(left, right)
		return left.key_type == right.key_type
	end,
	__tostring = function(self)
		return "terms-gen set key:<" .. tostring(self.key_type) .. ">"
	end,
}

local function gen_set_methods(self, key_type)
	return {
		put = function(val, key)
			if key_type.value_check(key) ~= true then
				p("set-put", key_type)
				p(key)
				error("wrong key type passed to set:put")
			end
			val._set[key] = true
		end,
		remove = function(val, key)
			if key_type.value_check(key) ~= true then
				p("set-remove", key_type)
				p(key)
				error("wrong key type passed to set:remove")
			end
			val._set[key] = nil
		end,
		test = function(val, key)
			if key_type.value_check(key) ~= true then
				p("set-test", key_type)
				p(key)
				error("wrong key type passed to set:test")
			end
			return val._set[key]
		end,
		-- just ignore the second value of the iterations :)
		pairs = function(val)
			return pairs(val._set)
		end,
		copy = function(val, onto)
			if not onto then
				onto = self()
			end
			local rt = getmetatable(onto)
			if self ~= rt then
				error("set:copy must be passed sets of the same type")
			end
			for k in val:pairs() do
				onto:put(k)
			end
			return onto
		end,
		union = function(left, right)
			local rt = getmetatable(right)
			if self ~= rt then
				error("set:union must be passed sets of the same type")
			end
			local new = left:copy()
			right:copy(new)
			return new
		end,
		subtract = function(left, right)
			local rt = getmetatable(right)
			if self ~= rt then
				error("set:subtract must be passed sets of the same type")
			end
			local new = left:copy()
			for k in right:pairs() do
				new:remove(k)
			end
			return new
		end,
		superset = function(left, right)
			local rt = getmetatable(right)
			if self ~= rt then
				error("set:superset must be passed sets of the same type")
			end
			for k in right:pairs() do
				if not left:test(k) then
					return false
				end
			end
			return true
		end,
	}
end

local set_memo = {}

---@param self table
---@param key_type Type
---@return SetType self
local function define_set(self, key_type)
	if type(key_type) ~= "table" or type(key_type.value_check) ~= "function" then
		error("trying to set the key or value type to something that isn't a type (possible typo?)")
	end

	if set_memo[key_type] then
		return set_memo[key_type]
	else
		set_memo[key_type] = self
	end

	setmetatable(self, set_type_mt)
	---@cast self SetType
	-- NOTE: this isn't primitive equality; this type has a __eq metamethod!
	self.value_check = metatable_equality(self)
	---@type SetDeriveInfo
	local derive_info = {
		key_type = key_type,
	}
	function self:derive(deriver, ...)
		return deriver.set(self, derive_info, ...)
	end
	self.key_type = key_type
	self.__index = gen_set_methods(self, key_type)
	self.__pairs = self.__index.pairs
	self:derive(derivers.pretty_print)
	self:derive(derivers.value_name)
	return self
end

---@class ArrayType: Type
---@field derive fun(self: ArrayType, deriver: Deriver, ...)
---@field value_type Type
---@field methods table
---@field __index function
---@field __newindex function
---@field __ipairs function(ArrayValue): function, ArrayValue, integer
---@field __len function(ArrayValue): integer
---@field derived_eq boolean?
---@field __eq function(ArrayValue, ArrayValue): boolean
---@field derived_pretty_print boolean?
---@field __tostring function(ArrayValue): string
---@field derived_diff boolean?

---@class ArrayValue: Value
---@field n integer
---@field array Value[]
---@field ipairs fun(ArrayValue): function, ArrayValue, integer
---@field len fun(ArrayValue): integer
---@field append fun(ArrayValue, Value)
---@field copy fun(ArrayValue, integer?, integer?): ArrayValue
---@field unpack fun(ArrayValue): ...
---@field pretty_print fun(ArrayValue, ...)
---@field default_print fun(ArrayValue, ...)
---@field diff fun(ArrayValue)

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
	__tostring = function(self)
		return "terms-gen array val:<" .. tostring(self.value_type) .. ">"
	end,
}

local function gen_array_methods(self, value_type)
	return {
		ipairs = function(val)
			return ipairs(val.array)
		end,
		len = function(val)
			return val.n
		end,
		append = function(val, value)
			val[val.n + 1] = value
		end,
		copy = function(val, first, last)
			first = first or 1
			last = last or val:len()
			local new = self()
			for i = first, last do
				new:append(val.array[i])
			end
			return new
		end,
		unpack = function(val)
			return table.unpack(val.array)
		end,
	}
end

local function gen_array_index_fns(t, value_type)
	local function index(self, key)
		local method = t.methods[key]
		if method then
			return method
		end
		if type(key) ~= "number" then
			p("array-index", value_type)
			p(key)
			error("wrong key type passed to array indexing")
		end
		-- check if integer
		-- there are many nice ways to do this in lua >=5.3
		-- unfortunately, this is not us
		if math.floor(key) ~= key then
			p(key)
			error("key passed to array indexing is not an integer")
		end
		if key < 1 or key > self.n then
			p(key, self.n)
			error("key passed to array indexing is out of bounds")
		end
		return self.array[key]
	end
	local function newindex(self, key, value)
		if type(key) ~= "number" then
			p("array-index", value_type)
			p(key)
			error("wrong key type passed to array index-assignment")
		end
		if math.floor(key) ~= key then
			p(key)
			error("key passed to array index-assignment is not an integer")
		end
		-- n+1 can be used to append
		if key < 1 or key > self.n + 1 then
			p(key, self.n)
			error("key passed to array index-assignment is out of bounds")
		end
		if value_type.value_check(value) ~= true then
			p("array-index-assign", value_type)
			p(value)
			error("wrong value type passed to array index-assignment")
		end
		self.array[key] = value
		if key > self.n then
			self.n = key
		end
	end
	return index, newindex
end

local array_memo = {}

---@param self table
---@param value_type Type
---@return ArrayType self
local function define_array(self, value_type)
	if type(value_type) ~= "table" or type(value_type.value_check) ~= "function" then
		error("trying to set the value type to something that isn't a type (possible typo?)")
	end

	if array_memo[value_type] then
		return array_memo[value_type]
	else
		array_memo[value_type] = self
	end

	setmetatable(self, array_type_mt)
	---@cast self ArrayType
	-- NOTE: this isn't primitive equality; this type has a __eq metamethod!
	self.value_check = metatable_equality(self)
	---@type ArrayDeriveInfo
	local derive_info = {
		value_type = value_type,
	}
	function self:derive(deriver, ...)
		return deriver.array(self, derive_info, ...)
	end
	self.value_type = value_type
	self.methods = gen_array_methods(self, value_type)
	self.__index, self.__newindex = gen_array_index_fns(self, value_type)
	self.__ipairs = self.methods.ipairs
	self.__len = self.methods.len
	self:derive(derivers.eq)
	self:derive(derivers.pretty_print)
	self:derive(derivers.diff)
	self:derive(derivers.value_name)
	return self
end

---@class UndefinedType: Type
---@field define_record fun(self: table, kind: string, params_with_types: ParamsWithTypes): RecordType
---@field define_enum fun(self: table, name: string, variants: Variants): EnumType
---@field define_foreign fun(self: table, value_check: ValueCheckFn, lsp_type: string): ForeignType
---@field define_map fun(self: table, key_type: Type, value_type: Type): MapType
---@field define_set fun(self: table, key_type: Type): SetType
---@field define_array fun(self: table, value_type: Type): ArrayType

local type_mt = {
	__index = {
		define_record = define_record,
		define_enum = define_enum,
		define_foreign = define_foreign,
		define_map = define_map,
		define_set = define_set,
		define_array = define_array,
	},
}

---@type ValueCheckFn
local function undefined_value_check(_)
	error("trying to typecheck a value against a type that has been declared but not defined")
end

---@param self table
---@return UndefinedType self
local function define_type(self)
	setmetatable(self, type_mt)
	self.value_check = undefined_value_check
	---@cast self UndefinedType
	return self
end

---@param typename string
---@return ForeignType
local function gen_builtin(typename)
	return define_foreign({}, function(val)
		return type(val) == typename
	end, typename)
end

local terms_gen = {
	---@type fun(kind: string, params_with_types: ParamsWithTypes): RecordType
	declare_record = new_self(define_record),
	---@type fun(name: string, variants: Variants): EnumType
	declare_enum = new_self(define_enum),
	-- Make sure the function you pass to this returns true, not just a truthy value
	---@type fun(value_check: ValueCheckFn, lsp_type: string): ForeignType
	declare_foreign = new_self(define_foreign),
	---@type fun(key_type: Type, value_type: Type): MapType
	declare_map = new_self(define_map),
	---@type fun(key_type: Type): SetType
	declare_set = new_self(define_set),
	---@type fun(value_type: Type): ArrayType
	declare_array = new_self(define_array),
	---@type fun(): UndefinedType
	declare_type = new_self(define_type),
	metatable_equality = metatable_equality,
	builtin_number = gen_builtin("number"),
	builtin_string = gen_builtin("string"),
	builtin_function = gen_builtin("function"),
	builtin_table = gen_builtin("table"),
	any_lua_type = define_foreign({}, function()
		return true
	end, "any"),
}
local internals_interface = require "./internals-interface"
internals_interface.terms_gen = terms_gen
return terms_gen
