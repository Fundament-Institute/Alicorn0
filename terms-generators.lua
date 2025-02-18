-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>
local derivers = require "derivers"
local pretty_printer = require "pretty-printer"
local traits = require "traits"
local U = require "alicorn-utils"

local _ = require "lua-ext" -- has side-effect of loading fixed table.concat

local math_floor, select, type = math.floor, select, type
local s = pretty_printer.s

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

---This attempts to create a traceback only if debug information is actually available
---@param s string
---@return string
local function attempt_traceback(s)
	if debug then
		return debug.traceback(s)
	else
		return s
	end
end

---@param mt table
---@return ValueCheckFn
local function metatable_equality(mt)
	if type(mt) ~= "table" then
		error(
			"trying to define metatable equality to something that isn't a metatable (possible typo?): "
				.. attempt_traceback(tostring(mt))
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
				attempt_traceback(
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
---@overload fun(...): RecordValue
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
			_record = {},
		}
		for i, v in ipairs(params) do
			local param = args[i]
			local param_type = params_types[i]
			-- type-check constructor arguments
			if param_type.value_check(param) ~= true then
				error(
					attempt_traceback(
						string.format(
							"wrong argument type passed to constructor %s, parameter %q\nexpected type of parameter %q is: %s\nvalue of parameter %q: (follows)\n%s",
							kind,
							v,
							v,
							param_type,
							v,
							s(param)
						)
					)
				)
			end
			val._record[v] = param
		end
		if false then
			-- val["{TRACE}"] = U.bound_here(2)
			val["{TRACE}"] = attempt_traceback("", 2)
			-- val["{TRACE}"] = U.custom_traceback("", "", -1)
		end
		val["{ID}"] = U.debug_id()
		setmetatable(val, self)
		return val
	end
	build_record = U.memoize(build_record, false)
	-- freeze args before entering memoized function
	-- because freeze may produce a hash-consed instance of the given arg
	-- which allows hash-consing to work with arrays etc
	local function build_record_freeze_wrapper(...)
		local args = { ... }
		for i, v in ipairs(params) do
			local argi = args[i]
			local freeze_impl = traits.freeze:get(params_types[i])
			if freeze_impl then
				argi = freeze_impl.freeze(params_types[i], argi)
			else
				print(
					"WARNING: while constructing "
						.. kind
						.. ", can't freeze param "
						.. v
						.. " (type "
						.. tostring(params_types[i])
						.. ")"
				)
				print("this may lead to suboptimal hash-consing")
			end
			args[i] = argi
		end
		-- adjust args to correct number so memoize works even given too many args
		-- (build_record won't error with too many args)
		return build_record(table.unpack(args, 1, #params))
	end
	setmetatable(cons, {
		__call = function(_, ...)
			return build_record_freeze_wrapper(...)
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
	self.__index = function(t, key)
		local method = self.methods[key]
		if method then
			return method
		end

		if key == "{TRACE}" or key == "{ID}" then
			return t._record[key]
		end
		if key ~= "name" then
			error(attempt_traceback("use unwrap instead for: " .. key))
		end
		if t._record[key] then
			return t._record[key]
		end

		error("Tried to access nonexistent key: " .. key)
	end
	self.methods = {
		pretty_preprint = pretty_printer.pretty_preprint,
		pretty_print = pretty_printer.pretty_print,
		default_print = pretty_printer.default_print,
	}
	self.__newindex = function()
		error("records are immutable!")
	end
	traits.value_name:implement_on(self, {
		value_name = function()
			return kind
		end,
	})
	self:derive(derivers.eq)
	self:derive(derivers.unwrap)
	self:derive(derivers.diff)
	self:derive(derivers.freeze)
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
---@overload fun(...): EnumValue
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
	self.__index = function(t, key)
		local method = self.methods[key]
		if method then
			return method
		end

		if key == "{TRACE}" or key == "{ID}" then
			return t._record[key]
		end
		error(attempt_traceback("use unwrap instead for: " .. key))
		if t._record[key] then
			return t._record[key]
		end

		error("Tried to access nonexistent key: " .. key)
	end
	self.methods = {
		pretty_preprint = pretty_printer.pretty_preprint,
		pretty_print = pretty_printer.pretty_print,
		default_print = pretty_printer.default_print,
	}
	self.__newindex = function()
		error("enums are immutable!")
	end
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
	self:derive(derivers.freeze)
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
---@param fn_specify fun(args: any[], types: Type[]) : string, any[]
---@param fn_unify fun(args: any[]) : any[]
---@param types { [string]: UndefinedType }
---@param names { [string]: string }
---@param variants Variants
---@param fn_sub fun(types: Type[])?
local function define_multi_enum(flex, flex_name, fn_replace, fn_specify, fn_unify, types, names, variants, fn_sub)
	---@type {[string]: Variants }
	local keyed_variants = {}
	---@type Variants
	local flex_variants = {}
	for _, k, v in U.table_stable_pairs(types) do
		keyed_variants[k] = {}
		table.insert(flex_variants, { k, { k, v } })
	end

	---@type {[string]: string }
	local flex_tags = {}

	for _, v in ipairs(variants) do
		local vname, vtag = table.unpack(split_delim(v[1], "$"))
		local vparams_with_types = v[2]
		if vtag == nil then
			error("Missing tag on " .. vname)
		end
		table.insert(flex_variants, { vname, vparams_with_types })
		flex_tags[vname] = vtag

		if vtag == "flex" then
			for _, k, _ in U.table_stable_pairs(types) do
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

	for _, k, v in U.table_stable_pairs(types) do
		v:define_enum(names[k], keyed_variants[k])
	end

	if fn_sub then
		fn_sub(types)
	end

	flex:define_enum(flex_name, flex_variants)

	local unify_passthrough = function(ok, ...)
		return ok, table.unpack(fn_unify(table.pack(...)))
	end

	for i, pair in ipairs(flex_variants) do
		local k = pair[1]
		if flex_tags[k] == "flex" then
			local vkind = flex_name .. "." .. k
			local params, params_types = parse_params_with_types(pair[2])
			validate_params_types(vkind, params, params_types)
			flex[k] = function(...)
				local args = table.pack(...)
				for i, v in ipairs(params) do
					local param = args[i]
					local param_type = params_types[i]
					if param_type.value_check(param) ~= true then
						error(
							attempt_traceback(
								string.format(
									"wrong argument type passed to constructor %s, parameter %q\nexpected type of parameter %q is: %s\nvalue of parameter %q: (follows)\n%s",
									param.kind,
									v,
									v,
									param_type,
									v,
									s(param)
								)
							)
						)
					end
				end
				local tag, unified_args = fn_specify(args, params_types)
				local subtype = types[tag]
				local inner = subtype[k](table.unpack(unified_args))
				return flex[tag](inner)
			end
		elseif flex_tags[k] ~= nil then
			local tag = flex_tags[k]
			local subtype = types[tag]
			local inner = subtype[k]
			if not pair[2] then
				flex[k] = flex[tag](inner)
			else
				flex[k] = function(...)
					return flex[tag](inner(...))
				end
			end
		end

		local derivers = { "is_", "unwrap_", "as_" }
		for _, v in ipairs(derivers) do
			local tag = flex_tags[k]
			local key = v .. k

			local unwrapper = {}
			for _, k, v in U.table_stable_pairs(types) do
				unwrapper[flex_name .. "." .. k] = flex.methods["unwrap_" .. k]
			end

			if tag == "flex" then
				if v == "is_" then
					flex.methods[key] = function(self, ...)
						local inner = unwrapper[self.kind](self)
						return inner[key](inner, ...)
					end
				elseif v == "unwrap_" then
					flex.methods[key] = function(self, ...)
						local inner = unwrapper[self.kind](self)
						return table.unpack(fn_unify(table.pack(inner[key](inner, ...))))
					end
				elseif v == "as_" then
					flex.methods[key] = function(self, ...)
						local inner = unwrapper[self.kind](self)
						return unify_passthrough(inner[key](inner, ...))
					end
				end
			elseif tag ~= nil then
				local base = flex.methods[key]
				if not base then
					error("Trying to override nonexistent function " .. key)
				end
				if v == "is_" or v == "as_" then
					flex.methods[key] = function(self, ...)
						local ok, inner = flex.methods["as_" .. tag](self)
						if not ok then
							return false
						end
						return inner[key](inner, ...)
					end
				elseif v == "unwrap_" then
					flex.methods[key] = function(self, ...)
						local inner = flex.methods[v .. tag](self)
						return inner[key](inner, ...)
					end
				end
			end
		end
	end

	--[[local lookup = {}
	for _, k, v in U.table_stable_pairs(types) do
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
---@overload fun(...): MapValue
---@field key_type Type
---@field value_type Type
---@field __index table
---@field __newindex function
---@field __pairs fun(self: MapValue): function, MapValue, Value?
---@field __tostring fun(self: MapValue): string

---@class MapValue<K, V>: Value, { K: V }
---@field _map { [Value]: Value }
---@field is_frozen boolean
---@field set fun(self: MapValue, key: Value, value: Value)
---@field reset fun(self: MapValue, key: Value)
---@field get fun(self: MapValue, key: Value): Value?
---@field pairs fun(self: MapValue): function, MapValue, Value?
---@field copy fun(self: MapValue, onto: MapValue?, conflict: function?): MapValue
---@field union fun(self: MapValue, right: MapValue, conflict: function): MapValue
---@field pretty_print fun(self: MapValue, ...)
---@field default_print fun(self: MapValue, ...)

local map_type_mt = {
	__call = function(self, ...)
		local val = {
			_map = {},
			is_frozen = false, -- bypass __newindex when setting is_frozen = true
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
			if val.is_frozen then
				error("trying to modify a frozen map")
			end
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
			local freeze_impl_key = traits.freeze:get(key_type)
			if freeze_impl_key then
				key = freeze_impl_key.freeze(key_type, key)
			else
				print(
					"WARNING: while setting "
						.. tostring(self)
						.. ", can't freeze key (type "
						.. tostring(key_type)
						.. ")"
				)
				print("this may lead to suboptimal hash-consing")
			end
			local freeze_impl_value = traits.freeze:get(value_type)
			if freeze_impl_value then
				value = freeze_impl_value.freeze(value_type, value)
			else
				print(
					"WARNING: while setting "
						.. tostring(self)
						.. ", can't freeze value (type "
						.. tostring(value_type)
						.. ")"
				)
				print("this may lead to suboptimal hash-consing")
			end
			val._map[key] = value
		end,
		reset = function(val, key)
			if val.is_frozen then
				error("trying to modify a frozen map")
			end
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

local function map_freeze_helper_2(t, ...)
	local frozenval = t(...)
	frozenval.is_frozen = true
	return frozenval
end
map_freeze_helper_2 = U.memoize(map_freeze_helper_2, false)

local function map_freeze_helper(t, keys, map, ...)
	if #keys > 0 then
		local key = table.remove(keys)
		local val = map[key]
		return map_freeze_helper(t, keys, map, key, val, ...)
	else
		return map_freeze_helper_2(t, ...)
	end
end

local function map_freeze(t, val)
	if val.is_frozen then
		return val
	end
	local order_impl = traits.order:get(t.key_type)
	if not order_impl then
		print("WARNING: can't freeze " .. tostring(t))
		return val
	end
	local keys = {}
	for k in pairs(val._map) do
		keys[#keys + 1] = k
	end
	table.sort(keys, order_impl.compare)
	local frozen = map_freeze_helper(t, keys, val._map)
	return frozen
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
			return ("MapValue<%s, %s>"):format(
				traits.value_name:get(key_type).value_name(),
				traits.value_name:get(value_type).value_name()
			)
		end,
	})
	traits.freeze:implement_on(self, { freeze = map_freeze })
	return self
end
define_map = U.memoize(define_map, false)

---@param key_type Type
---@param value_type Type
---@return MapType self
local function declare_map(key_type, value_type)
	return define_map({}, key_type, value_type)
end
declare_map = U.memoize(declare_map, false)

---@class SetType: Type
---@overload fun(...): SetValue
---@field key_type Type
---@field __index table
---@field __pairs fun(SetValue): function, SetValue, Value?
---@field __tostring fun(SetValue): string

---@class SetValue<K>: Value, { K: boolean }
---@field _set { [Value]: boolean }
---@field is_frozen boolean
---@field put fun(self: SetValue, key: Value)
---@field remove fun(self: SetValue, key: Value)
---@field test fun(self: SetValue, key: Value): boolean?
---@field pairs fun(self: SetValue): function, SetValue, Value?
---@field copy fun(self: SetValue, onto: SetValue?): SetValue
---@field union fun(self: SetValue, right: SetValue): SetValue
---@field subtract fun(self: SetValue, right: SetValue): SetValue
---@field superset fun(self: SetValue, right: SetValue): boolean
---@field pretty_print fun(self: SetValue, ...)
---@field default_print fun(self: SetValue, ...)

local set_type_mt = {
	__call = function(self, ...)
		local val = {
			_set = {},
			is_frozen = false,
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
			if val.is_frozen then
				error("trying to modify a frozen set")
			end
			if key_type.value_check(key) ~= true then
				p("set-put", key_type)
				p(key)
				error("wrong key type passed to set:put")
			end
			local freeze_impl_key = traits.freeze:get(key_type)
			if freeze_impl_key then
				key = freeze_impl_key.freeze(key_type, key)
			else
				print(
					"WARNING: while putting "
						.. tostring(self)
						.. ", can't freeze key (type "
						.. tostring(key_type)
						.. ")"
				)
				print("this may lead to suboptimal hash-consing")
			end
			val._set[key] = true
		end,
		remove = function(val, key)
			if val.is_frozen then
				error("trying to modify a frozen set")
			end
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

local function set_freeze_helper_2(t, ...)
	local frozenval = t(...)
	frozenval.is_frozen = true
	return frozenval
end
set_freeze_helper_2 = U.memoize(set_freeze_helper_2, false)

local function set_freeze_helper(t, keys, ...)
	if #keys > 0 then
		local key = table.remove(keys)
		return set_freeze_helper(t, keys, key, ...)
	else
		return set_freeze_helper_2(t, ...)
	end
end

local function set_freeze(t, val)
	if val.is_frozen then
		return val
	end
	local order_impl = traits.order:get(t.key_type)
	if not order_impl then
		print("WARNING: can't freeze " .. tostring(t))
		return val
	end
	local keys = {}
	for k in pairs(val._set) do
		keys[#keys + 1] = k
	end
	table.sort(keys, order_impl.compare)
	local frozen = set_freeze_helper(t, keys)
	return frozen
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
			return ("SetValue<%s>"):format(traits.value_name:get(key_type).value_name())
		end,
	})
	traits.freeze:implement_on(self, { freeze = set_freeze })
	return self
end
define_set = U.memoize(define_set, false)

---@param key_type Type
---@return SetType self
local function declare_set(key_type)
	return define_set({}, key_type)
end
declare_set = U.memoize(declare_set, false)

---@class ArrayType: Type
---@overload fun(...): ArrayValue
---@field value_type Type
---@field methods { [string]: function }
---@field __eq fun(ArrayValue, ArrayValue): boolean
---@field __index fun(self: ArrayValue, key: integer | string) : Value | function
---@field __newindex fun(self: ArrayValue, key: integer, value: Value)
---@field __ipairs fun(self: ArrayValue): function, ArrayValue, integer
---@field __len fun(self: ArrayValue): integer
---@field __tostring fun(self: ArrayValue): string

---@class ArrayValue<T>: Value, { [integer]: T }
---@field n integer
---@field array Value[]
---@field is_frozen boolean
---@field ipairs fun(self: ArrayValue): function, ArrayValue, integer
---@field len fun(self: ArrayValue): integer
---@field append fun(self: ArrayValue, v: Value)
---@field copy fun(self: ArrayValue, integer?, integer?): ArrayValue
---@field map fun(self: ArrayValue, target: ArrayType, fn: fun(any) : any): ArrayValue
---@field get fun(self: MapValue, key: Value): Value?
---@field unpack fun(self: ArrayValue): ...
---@field pretty_print fun(self: ArrayValue, ...)
---@field default_print fun(self: ArrayValue, ...)

local array_type_mt = {
	__call = function(self, ...)
		local value_type = self.value_type
		local array, n = {}, select("#", ...)
		for i = 1, n do
			local value = select(i, ...)
			if value_type.value_check(value) ~= true then
				error(
					attempt_traceback(
						string.format(
							"wrong value type passed to array creation: expected [%s] of type %s but got %s",
							s(i),
							s(value_type),
							s(value)
						)
					)
				)
			end
			array[i] = value
		end
		return setmetatable({
			array = array,
			is_frozen = false,
			n = n,
		}, self)
	end,
	__eq = function(left, right)
		return left.value_type == right.value_type
	end,
	__tostring = function(self)
		return "terms-gen array val:<" .. tostring(self.value_type) .. ">"
	end,
}

local function array_unchecked_new_fn(self, array, n)
	local value_type = self.value_type
	local new_array = {}
	if n == nil then
		n = array.n
		if n == nil then
			n = #array
		end
	end
	for i = 1, n do
		new_array[i] = array[i]
	end
	return setmetatable({
		n = n,
		array = new_array,
		is_frozen = false,
	}, self)
end

local function array_new_fn(self, array, n)
	local value_type = self.value_type
	local new_array = {}
	if n == nil then
		n = array.n
		if n == nil then
			n = #array
		end
	end
	for i = 1, n do
		local value = array[i]
		if value_type.value_check(value) ~= true then
			error(
				attempt_traceback(
					string.format(
						"wrong value type passed to array creation: expected [%s] of type %s but got %s",
						s(i),
						s(value_type),
						s(value)
					)
				)
			)
		end
		new_array[i] = value
	end
	return setmetatable({
		n = n,
		array = new_array,
		is_frozen = false,
	}, self)
end

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
			if val.is_frozen then
				error("trying to modify a frozen array")
			end
			local n = val.n + 1
			val.array[n], val.n = value, n
		end,
		copy = function(val, first, last)
			first = first or 1
			last = last or val.n
			local array, new_array = val.array, {}
			for i = first, last do
				new_array[i] = array[i]
			end
			return self:unchecked_new(new_array, n)
		end,
		unpack = function(val)
			return table.unpack(val.array, 1, val.n)
		end,
		map = function(val, to, fn)
			local value_type = to.value_type
			local array, new_array, n = val.array, {}, val.n
			for i = 1, n do
				local value = fn(array[i])
				if value_type.value_check(value) ~= true then
					error(
						attempt_traceback(
							string.format(
								"wrong value type resulting from array mapping: expected [%s] of type %s but got %s",
								s(i),
								s(value_type),
								s(value)
							)
						)
					)
				end
				new_array[i] = value
			end

			return to:unchecked_new(new_array, n)
		end,
		get = function(val, key)
			return val.array[key]
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
		if math_floor(key) ~= key then
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
		if val.is_frozen then
			error(string.format("trying to set %s on a frozen array to %s: %s", s(key), s(value), s(val)))
		end
		if type(key) ~= "number" then
			error(
				string.format(
					"wrong key type passed to array index-assignment: expected %s but got %s",
					s(value_type),
					s(key)
				)
			)
		end
		if math_floor(key) ~= key then
			error(string.format("key passed to array index-assignment is not an integer: %s", s(key)))
		end
		-- n+1 can be used to append
		if key < 1 or key > val.n + 1 then
			error(string.format("key %s passed to array index-assignment is out of bounds: %s", s(key), s(val.n)))
		end
		if value_type.value_check(value) ~= true then
			error(
				attempt_traceback(
					string.format(
						"wrong value type passed to array index-assignment: expected [%s] of type %s but got %s",
						s(key),
						s(value_type),
						s(value)
					)
				)
			)
		end
		local freeze_impl_value = traits.freeze:get(value_type)
		if freeze_impl_value then
			value = freeze_impl_value.freeze(value_type, value)
		else
			print(
				"WARNING: while setting "
					.. tostring(self)
					.. ", can't freeze value (type "
					.. tostring(value_type)
					.. ")"
			)
			print("this may lead to suboptimal hash-consing")
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

local function array_freeze_helper(t, n)
	local function array_freeze_helper_aux(array)
		local frozenval = t:new(array, n)
		frozenval.is_frozen = true
		return frozenval
	end
	array_freeze_helper_aux = U.memoize(array_freeze_helper_aux, true)
	return array_freeze_helper_aux
end
array_freeze_helper = U.memoize(array_freeze_helper, false)

local function array_freeze(t, val)
	if val.is_frozen then
		return val
	end
	local frozen = array_freeze_helper(t, val.n)(val.array)
	return frozen
end

---@param self table
---@param value_type Type
---@return ArrayType self
local function define_array(self, value_type)
	if type(value_type) ~= "table" or type(value_type.value_check) ~= "function" then
		error(
			"trying to set the value type to something that isn't a type (possible typo?): "
				.. attempt_traceback(tostring(value_type))
		)
	end

	setmetatable(self, array_type_mt)
	---@cast self ArrayType
	self.unchecked_new = array_unchecked_new_fn
	self.new = array_new_fn
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
			return ("ArrayValue<%s>"):format(traits.value_name:get(value_type).value_name())
		end,
	})
	traits.freeze:implement_on(self, { freeze = array_freeze })
	return self
end
define_array = U.memoize(define_array, false)

---@param value_type Type
---@return ArrayType self
local function declare_array(value_type)
	return define_array({}, value_type)
end
declare_array = U.memoize(declare_array, false)

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
	---@type fun(kind: string, params_with_types: ParamsWithTypes): (self: RecordType)
	declare_record = new_self(define_record),
	---@type fun(name: string, variants: Variants): (self: EnumType)
	declare_enum = new_self(define_enum),
	-- Make sure the function you pass to this returns true, not just a truthy value
	---@type fun(value_check: ValueCheckFn, lsp_type: string): (self: ForeignType)
	declare_foreign = new_self(define_foreign),
	declare_map = declare_map,
	declare_set = declare_set,
	declare_array = declare_array,
	---@type fun(): (self: UndefinedType)
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

-- lua numbers and strings are immutable
-- additionally, strings are already interned by the interpreter
local function freeze_trivial(t, val)
	return val
end
-- lua numbers and strings are always comparable
-- NOTE: strings are compared by locale collation
--       so don't change locale during runtime
local function compare_trivial(left, right)
	return left < right
end
for _, t in ipairs { terms_gen.builtin_number, terms_gen.builtin_string } do
	traits.freeze:implement_on(t, { freeze = freeze_trivial })
	traits.order:implement_on(t, { compare = compare_trivial })
end
-- lua tables are often used as unique ids
for _, t in ipairs { terms_gen.builtin_table, terms_gen.any_lua_type } do
	traits.freeze:implement_on(t, { freeze = freeze_trivial })
end

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
