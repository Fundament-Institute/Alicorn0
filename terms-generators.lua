local derivers = require "derivers"
local pretty_printer = require "pretty-printer"
local traits = require "traits"
local U = require "alicorn-utils"

local _ = require "lua-ext" -- has side-effect of loading fixed table.concat

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
		error(
			"trying to define metatable equality to something that isn't a metatable (possible typo?): "
				.. debug.traceback(tostring(mt))
		)
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
				debug.traceback(
					"trying to set a parameter type to something that isn't a type, in constructor "
						.. kind
						.. ", parameter "
						.. v
						.. " (possible typo?)"
				)
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
---@field __eq fun(left: RecordValue, right: RecordValue): boolean
---@field __index table
---@field __tostring function(RecordValue): string

---@class RecordValue: Value
---@field pretty_print fun(RecordValue, ...)
---@field default_print fun(RecordValue, ...)

---@param self table
---@param cons table
---@param kind string
---@param params_with_types ParamsWithTypes
---@return RecordDeriveInfo derive_info
local function gen_record(self, cons, kind, params_with_types)
	local params, params_types = parse_params_with_types(params_with_types)
	validate_params_types(kind, params, params_types)
	local function build_record(...)
		local args = table.pack(...)
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
				error(
					debug.traceback("wrong argument type passed to constructor " .. kind .. ", parameter '" .. v .. "'")
				)
			end
			val[v] = argi
		end
		val["{TRACE}"] = U.bound_here(2) -- debug.traceback()
		val["{ID}"] = U.debug_id()
		setmetatable(val, self)
		return val
	end
	setmetatable(cons, {
		__call = function(_, ...)
			return build_record(...)
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
	self.__index = {
		pretty_preprint = pretty_printer.pretty_preprint,
		pretty_print = pretty_printer.pretty_print,
		default_print = pretty_printer.default_print,
	}
	traits.value_name:implement_on(self, {
		value_name = function()
			return kind
		end,
	})
	self:derive(derivers.eq)
	self:derive(derivers.unwrap)
	self:derive(derivers.diff)
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
---@field __eq fun(left: EnumValue, right: EnumValue): boolean
---@field __index table
---@field __tostring function(EnumValue): string

---@class EnumValue: Value
---@field pretty_print fun(EnumValue, ...) : string
---@field default_print fun(EnumValue, ...)

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
	self.__index = {
		pretty_preprint = pretty_printer.pretty_preprint,
		pretty_print = pretty_printer.pretty_print,
		default_print = pretty_printer.default_print,
	}
	traits.value_name:implement_on(self, {
		value_name = function()
			return name
		end,
	})
	self:derive(derivers.eq)
	self:derive(derivers.is)
	self:derive(derivers.unwrap)
	self:derive(derivers.as)
	self:derive(derivers.diff)
	return self
end

---@param s string
---@param delim string
---@return string[]
local function split_delim(s, delim)
	local subs = {}
	-- This might have an extra blank match at the end but we actually don't care in this case
	for sub in s:gmatch("[^" .. delim .. "]+") do
		table.insert(subs, sub)
	end
	return subs
end

---@param flex UndefinedType
---@param flex_name string
---@param fn_replace fun(tag: string, variant: Type) : Type
---@param fn_unify fun(args: any[], types: Type[]) : string, any[]
---@param types { [string]: UndefinedType }
---@param names { [string]: string }
---@param variants Variants
local function define_multi_enum(flex, flex_name, fn_replace, fn_unify, types, names, variants)
	---@type {[string]: Variants }
	local keyed_variants = {}
	---@type Variants
	local flex_variants = {}
	for k, v in pairs(types) do
		keyed_variants[k] = {}
		table.insert(flex_variants, { k, { k, v } })
	end

	---@type {[string]: string }
	local flex_tags = {}

	for i, v in ipairs(variants) do
		local vname, vtag = table.unpack(split_delim(v[1], "$"))
		local vparams_with_types = v[2]
		if vtag == nil then
			error("Missing tag on " .. vname)
		end
		table.insert(flex_variants, { vname, vparams_with_types })
		flex_tags[vname] = vtag

		if vtag == "flex" then
			for k, _ in pairs(types) do
				local fix_variants = {}
				for i, ty in ipairs(vparams_with_types) do
					if (i % 2) == 0 and fn_replace then
						table.insert(fix_variants, fn_replace(k, ty))
					else
						table.insert(fix_variants, ty)
					end
				end
				table.insert(keyed_variants[k], { vname, fix_variants })
			end
		else
			if keyed_variants[vtag] == nil then
				error("Unknown tag: " .. vtag)
			end
			table.insert(keyed_variants[vtag], { vname, vparams_with_types })
		end
	end

	for k, v in pairs(types) do
		v:define_enum(names[k], keyed_variants[k])
	end

	flex:define_enum(flex_name, flex_variants)

	for i, pair in ipairs(flex_variants) do
		local k = pair[1]
		if flex_tags[k] == "flex" then
			local vkind = flex_name .. "." .. k
			local params, params_types = parse_params_with_types(pair[2])
			validate_params_types(vkind, params, params_types)
			flex[k] = function(...)
				local args = table.pack(...)
				for i, v in ipairs(params) do
					if params_types[i].value_check(args[i]) ~= true then
						error(
							debug.traceback(
								"wrong argument type passed to constructor " .. kind .. ", parameter '" .. v .. "'"
							)
						)
					end
				end
				local tag, unified_args = fn_unify(args, params_types)
				local subtype = types[tag]
				local inner = subtype[k](table.unpack(unified_args))
				return flex[tag](inner)
			end
		elseif flex_tags[k] ~= nil then
			local tag = flex_tags[k]
			local subtype = types[tag]
			local inner = subtype[k]
			flex[k] = function(...)
				return flex[tag](inner(...))
			end
		end

		local derivers = { "is_", "unwrap_", "as_" }
		for _, v in ipairs(derivers) do
			local tag = flex_tags[k]
			if tag == "flex" then
				error("NYI")
			elseif tag ~= nil then
				local base = flex.__index[v .. k]
				if not base then
					error("Trying to override nonexistent function " .. v .. k)
				end
				if v == "is_" or v == "as_" then
					flex.__index[v .. k] = function(self, ...)
						local ok, inner = flex["as_" .. tag](self)
						if not ok then
							return false
						end
						return inner[v .. k](inner, ...)
					end
				elseif v == "unwrap_" then
					flex.__index[v .. k] = function(self, ...)
						local inner = flex[v .. tag](self)
						return inner[v .. k](inner, ...)
					end
				end
			end
		end
	end

	--[[local lookup = {}
	for k, v in pairs(types) do
		lookup[flex_name .. "." .. k] = k
	end

	for _, k in ipairs(forward) do
		local derivers = { "is_", "unwrap_", "as_" }

		for _, v in ipairs(derives) do
			flex[v .. k] = function(self, ...)
				local child = self[ lookup[self.kind] ]
				child[v .. k](child, ...)
			end
		end
	end]]
end

---@class ForeignType: Type
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
	self.lsp_type = lsp_type
	traits.value_name:implement_on(self, {
		value_name = function()
			return lsp_type
		end,
	})
	return self
end

---@class MapType: Type
---@field key_type Type
---@field value_type Type
---@field __index table
---@field __newindex function
---@field __pairs function(MapValue): function, MapValue, Value?
---@field __tostring function(MapValue): string

---@class MapValue: Value
---@field _map { [Value]: Value }
---@field set fun(MapValue, Value, Value)
---@field reset fun(MapValue, Value)
---@field get fun(MapValue, Value): Value?
---@field pairs fun(MapValue): function, MapValue, Value?
---@field copy fun(MapValue, MapValue?, function?): MapValue
---@field union fun(MapValue, MapValue, function): MapValue
---@field pretty_print fun(MapValue, ...)
---@field default_print fun(MapValue, ...)

local map_type_mt = {
	__call = function(self, ...)
		local val = {
			_map = {},
		}
		setmetatable(val, self)
		local args = table.pack(...)
		for i = 1, args.n, 2 do
			val:set(args[i], args[i + 1])
		end
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
		copy = function(val, onto, conflict)
			if not onto then
				onto = self()
			elseif not conflict then
				error("map:copy onto requires a conflict resolution function")
			end
			local rt = getmetatable(onto)
			if self ~= rt then
				error("map:copy must be passed maps of the same type")
			end
			for k, v in val:pairs() do
				local old = onto:get(k)
				if old then
					onto:set(k, conflict(old, v))
				else
					onto:set(k, v)
				end
			end
			return onto
		end,
		union = function(left, right, conflict)
			local rt = getmetatable(right)
			if self ~= rt then
				error("map:union must be passed maps of the same type")
			end
			local new = left:copy()
			right:copy(new, conflict)
			return new
		end,
		pretty_preprint = pretty_printer.pretty_preprint,
		pretty_print = pretty_printer.pretty_print,
		default_print = pretty_printer.default_print,
	}
end

local function map_newindex()
	error("index-assignment of maps is no longer allowed. use :set()")
end

local function map_pretty_print(self, pp, ...)
	return pp:table(self._map, ...)
end

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

	setmetatable(self, map_type_mt)
	---@cast self MapType
	-- NOTE: this isn't primitive equality; this type has a __eq metamethod!
	self.value_check = metatable_equality(self)
	self.key_type = key_type
	self.value_type = value_type
	self.__index = gen_map_methods(self, key_type, value_type)
	self.__newindex = map_newindex
	self.__pairs = self.__index.pairs
	self.__tostring = self.__index.pretty_print
	traits.pretty_print:implement_on(self, {
		pretty_print = map_pretty_print,
		default_print = map_pretty_print,
	})
	traits.value_name:implement_on(self, {
		value_name = function()
			-- TODO: augment this with generics
			return "MapValue"
		end,
	})
	return self
end
define_map = U.memoize(define_map)

---@class SetType: Type
---@field key_type Type
---@field __index table
---@field __pairs function(SetValue): function, SetValue, Value?
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
	__call = function(self, ...)
		local val = {
			_set = {},
		}
		setmetatable(val, self)
		local args = table.pack(...)
		for i = 1, args.n do
			val:put(args[i])
		end
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
		pretty_preprint = pretty_printer.pretty_preprint,
		pretty_print = pretty_printer.pretty_print,
		default_print = pretty_printer.default_print,
	}
end

local function set_pretty_print(self, pp, ...)
	return pp:table(self._set, ...)
end

---@param self table
---@param key_type Type
---@return SetType self
local function define_set(self, key_type)
	if type(key_type) ~= "table" or type(key_type.value_check) ~= "function" then
		error("trying to set the key or value type to something that isn't a type (possible typo?)")
	end

	setmetatable(self, set_type_mt)
	---@cast self SetType
	-- NOTE: this isn't primitive equality; this type has a __eq metamethod!
	self.value_check = metatable_equality(self)
	self.key_type = key_type
	self.__index = gen_set_methods(self, key_type)
	self.__pairs = self.__index.pairs
	self.__tostring = self.__index.pretty_print
	traits.pretty_print:implement_on(self, {
		pretty_print = set_pretty_print,
		default_print = set_pretty_print,
	})
	traits.value_name:implement_on(self, {
		value_name = function()
			-- TODO: augment this with generics
			return "SetValue"
		end,
	})
	return self
end
define_set = U.memoize(define_set)

---@class ArrayType: Type
---@field value_type Type
---@field methods { [string]: function }
---@field __eq fun(ArrayValue, ArrayValue): boolean
---@field __index fun(self: ArrayValue, key: integer | string) : Value | function
---@field __newindex fun(self: ArrayValue, key: integer, value: Value)
---@field __ipairs fun(ArrayValue): function, ArrayValue, integer
---@field __len fun(ArrayValue): integer
---@field __tostring fun(ArrayValue): string

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

local array_type_mt = {
	__call = function(self, ...)
		local val = {
			n = 0,
			array = {},
		}
		setmetatable(val, self)
		local args = table.pack(...)
		for i = 1, args.n do
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

---@param state ArrayValue
---@param control integer
---@return integer?
---@return Value?
local function array_next(state, control)
	local i = control + 1
	if i > state:len() then
		return nil
	else
		return i, state[i]
	end
end

local function gen_array_methods(self, value_type)
	return {
		ipairs = function(val)
			return array_next, val, 0
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
			return table.unpack(val.array, 1, val.n)
		end,
		map = function(val, to, fn)
			local x = {}
			for i = 1, val:len() do
				x[i] = fn(val.array[i])
			end

			return to(table.unpack(x, 1, val:len()))
		end,
		pretty_preprint = pretty_printer.pretty_preprint,
		pretty_print = pretty_printer.pretty_print,
		default_print = pretty_printer.default_print,
	}
end

local function array_eq_fn(left, right)
	if getmetatable(left) ~= getmetatable(right) then
		return false
	end
	if left:len() ~= right:len() then
		return false
	end
	for i = 1, left:len() do
		if left[i] ~= right[i] then
			return false
		end
	end
	return true
end

---@generic V : Type
---@param self ArrayType
---@param value_type `V`
---@return fun(self: ArrayValue, key: integer | string) : V | function
---@return fun(self: ArrayValue, key: integer, value: V)
local function gen_array_index_fns(self, value_type)
	---@param val ArrayValue
	---@param key integer | string
	---@return Value | function
	local function index(val, key)
		local method = self.methods[key]
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
		-- unfortunately, this is not part of luajit/luvit
		if math.floor(key) ~= key then
			p(key)
			error("key passed to array indexing is not an integer")
		end
		-- puc-rio lua 5.3 ipairs() always produces an iterator that looks for the first nil
		-- instead of deferring to __ipairs metamethod like in 5.2
		--if key == val.n + 1 then
		--	return nil
		--end
		-- above is commented out because it turns out we want nil-resistant iterators
		-- so we should make sure to use the :ipairs() method instead
		if key < 1 or key > val.n then
			p(key, val.n)
			error(
				"key passed to array indexing is out of bounds (read code comment above): "
					.. tostring(key)
					.. " is not within [1,"
					.. tostring(val.n)
					.. "]"
			)
		end
		return val.array[key]
	end
	---@param val ArrayValue
	---@param key integer
	---@param value Value
	local function newindex(val, key, value)
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
		if key < 1 or key > val.n + 1 then
			p(key, val.n)
			error("key passed to array index-assignment is out of bounds")
		end
		if value_type.value_check(value) ~= true then
			p("array-index-assign", value_type)
			p(value)
			error("wrong value type passed to array index-assignment")
		end
		val.array[key] = value
		if key > val.n then
			val.n = key
		end
	end
	return index, newindex
end

local function array_pretty_print(self, pp, ...)
	return pp:array(self.array, ...)
end

local function gen_array_diff_fn(self, value_type)
	local function diff_fn(left, right)
		print("diffing array with value_type: " .. tostring(value_type))
		local rt = getmetatable(right)
		if self ~= rt then
			print("unequal types!")
			print(self)
			print(rt)
			print("stopping diff")
			return
		end
		if left:len() ~= right:len() then
			print("unequal lengths!")
			print(left:len())
			print(right:len())
			print("stopping diff")
			return
		end
		local n = 0
		local diff_elems = {}
		for i = 1, left:len() do
			if left[i] ~= right[i] then
				n = n + 1
				diff_elems[n] = i
			end
		end
		if n == 0 then
			print("no difference")
			print("stopping diff")
			return
		elseif n == 1 then
			local d = diff_elems[1]
			print("difference in element: " .. tostring(d))
			local diff_impl = traits.diff:get(value_type)
			if diff_impl then
				-- tail call
				return diff_impl.diff(left[d], right[d])
			else
				print("stopping diff (missing diff impl)")
				print("value_type:", value_type)
				return
			end
		else
			print("difference in multiple elements:")
			for i = 1, n do
				print(diff_elems[i])
			end
			print("stopping diff")
			return
		end
	end
	return diff_fn
end

---@param self table
---@param value_type Type
---@return ArrayType
local function define_array(self, value_type)
	if type(value_type) ~= "table" or type(value_type.value_check) ~= "function" then
		error(
			"trying to set the value type to something that isn't a type (possible typo?): "
				.. debug.traceback(tostring(value_type))
		)
	end

	setmetatable(self, array_type_mt)
	---@cast self ArrayType
	-- NOTE: this isn't primitive equality; this type has a __eq metamethod!
	self.value_check = metatable_equality(self)
	self.value_type = value_type
	self.methods = gen_array_methods(self, value_type)
	self.__eq = array_eq_fn
	self.__index, self.__newindex = gen_array_index_fns(self, value_type)
	self.__ipairs = self.methods.ipairs
	self.__len = self.methods.len
	self.__tostring = self.methods.pretty_print
	traits.pretty_print:implement_on(self, {
		pretty_print = array_pretty_print,
		default_print = array_pretty_print,
	})
	traits.diff:implement_on(self, {
		diff = gen_array_diff_fn(self, value_type),
	})
	traits.value_name:implement_on(self, {
		value_name = function()
			-- TODO: augment this with generics
			return "ArrayValue"
		end,
	})
	return self
end
define_array = U.memoize(define_array)

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
	array_type_mt = array_type_mt,
	define_multi_enum = define_multi_enum,
	any_lua_type = define_foreign({}, function()
		return true
	end, "any"),
}

local function any_lua_type_diff_fn(left, right)
	if type(left) ~= type(right) then
		print("different primitive lua types!")
		print(type(left))
		print(type(right))
		print("stopping diff")
		return
	end
	local dispatch = {
		["nil"] = function()
			print("diffing lua nils")
			print("no difference")
			print("stopping diff")
			return
		end,
		["number"] = function()
			print("diffing lua numbers")
			if left ~= right then
				print("different numbers")
				print(left)
				print(right)
				print("stopping diff")
				return
			end
			print("no difference")
			print("stopping diff")
			return
		end,
		["string"] = function()
			print("diffing lua strings")
			if left ~= right then
				print("different strings")
				print(left)
				print(right)
				print("stopping diff")
				return
			end
			print("no difference")
			print("stopping diff")
			return
		end,
		["boolean"] = function()
			print("diffing lua booleans")
			if left ~= right then
				print("different booleans")
				print(left)
				print(right)
				print("stopping diff")
				return
			end
			print("no difference")
			print("stopping diff")
			return
		end,
		["table"] = function()
			print("diffing lua tables")
			if left == right then
				print("physically equal")
				print("stopping diff")
				return
			end
			local n = 0
			local diff_elems = {}
			for k, lval in pairs(left) do
				rval = right[k]
				if lval ~= rval then
					n = n + 1
					diff_elems[n] = k
				end
			end
			for k, rval in pairs(right) do
				lval = left[k]
				if not lval then
					n = n + 1
					diff_elems[n] = k
				end
			end
			if n == 0 then
				print("no elements different")
				print("stopping diff")
				return
			elseif n == 1 then
				local d = diff_elems[1]
				print("difference in element: " .. tostring(d))
				local mtl = getmetatable(left[d])
				local mtr = getmetatable(right[d])
				if mtl ~= mtr then
					print("stopping diff (different metatables)")
					return
				end
				local diff_impl = traits.diff:get(mtl)
				if diff_impl then
					-- tail call
					return diff_impl.diff(left[d], right[d])
				else
					print("stopping diff (missing diff impl)")
					print("mt:", mtl)
					return
				end
			else
				print("difference in multiple elements:")
				for i = 1, n do
					print(diff_elems[i])
				end
				print("stopping diff")
				return
			end
		end,
		["function"] = function()
			print("diffing lua functions")
			if left ~= right then
				print("different functions")
				print(left)
				print(right)
				print("stopping diff")
				return
			end
			print("no difference")
			print("stopping diff")
			return
		end,
		["thread"] = function()
			print("diffing lua threads")
			if left ~= right then
				print("different threads")
				print(left)
				print(right)
				print("stopping diff")
				return
			end
			print("no difference")
			print("stopping diff")
			return
		end,
		["userdata"] = function()
			print("diffing lua userdatas")
			if left ~= right then
				print("different userdata")
				print(left)
				print(right)
				print("stopping diff")
				return
			end
			print("no difference")
			print("stopping diff")
			return
		end,
	}
	dispatch[type(left)]()
end
traits.diff:implement_on(terms_gen.any_lua_type, { diff = any_lua_type_diff_fn })

local internals_interface = require "internals-interface"
internals_interface.terms_gen = terms_gen
return terms_gen
