local terms = require "terms"
local gen = require "terms-generators"
local derivers = require "derivers"

---@class SerializedEnum
---@field kind string
---@field args integer[]

---@class EnumSerializationState
---@field construction SerializedEnum[]
---@field lookup {[any] : integer}

---@class SerializationState
---@field host_intrinsics string[]
---@field host_intrinsics_lookup {[string] : integer}
---@field metavariable_lookup {[Metavariable] : integer}
---@field metavariable_count integer
---@field enums {[string] : EnumSerializationState}

---@alias SerializedID integer

---@type {[Type] : fun(SerializationState, any) : SerializedID}
local serializers = {}
---@type {[Type] : fun(SerializationState, SerializedID) : unknown}
local serializers = {}
local deserializers = {}

---serialize a value of unknown type
---@param state SerializationState
---@param subject any
---@return SerializedID
local function serialize(state, subject) end

---deserialize a value of unknown type
---@param state SerializationState
---@param id SerializedID
---@return any
local function deserialize(state, id) end
---serialize a value of a known type
---@param state SerializationState
---@param stype Type
---@param subject any
---@return SerializedID
local function serialize_known(state, stype, subject)
	if not serializers[stype] then
		error "known type has no serializer implemented"
	end
	return serializers[type](state, subject)
end
---deserialize a value of a known type
---@param state SerializationState
---@param stype Type
---@param id SerializedID
---@return any
local function deserialize_known(state, stype, id)
	if not deserializers[stype] then
		error "known type has no deserializer implemented"
	end
	return deserializers[type](state, id)
end

---@type Deriver
-- TODO: boilerplate done, implement actual serialize
local serialize_deriver = {
	record = function(t, info)
		if t.derived_serialize then
			-- already derived, don't derive again
			return
		end

		local idx = t.__index or {}
		t.__index = idx
		local kind = info.kind
		local params = info.params

		local function serialize_fn(self)
			-- this function runs when you do myrecordterm:serialize()
		end
		idx.serialize = serialize_fn

		t.derived_serialize = true
	end,
	enum = function(t, info)
		if t.derived_serialize then
			-- already derived, don't derive again
			return
		end

		local idx = t.__index or {}
		t.__index = idx
		local name = info.name
		local variants = info.variants

		for _, vname in ipairs(variants) do
			local vkind = name .. "." .. vname
			local vdata = variants[vname]
			local vtype = vdata.type
			local vinfo = vdata.info
			if vtype == derivers.EnumDeriveInfoVariantKind.Record then
				for i, param in ipairs(vinfo.params) do
				end
			elseif vtype == derivers.EnumDeriveInfoVariantKind.Unit then
			else
				error("unknown variant type: " .. vtype)
			end
		end

		local function serialize_fn(self)
			-- this function runs when you do myenumterm:serialize()
		end
		idx.serialize = serialize_fn

		t.derived_serialize = true
	end,
	foreign = function()
		error("can't derive :serialize() for a foreign type")
	end,
	map = function(t, info)
		if t.derived_serialize then
			-- already derived, don't derive again
			return
		end

		local idx = t.__index

		local function serialize_fn(self) end
		idx.serialize = serialize_fn

		t.derived_serialize = true
	end,
	set = function(t, info)
		if t.derived_serialize then
			-- already derived, don't derive again
			return
		end

		local idx = t.__index

		local function serialize_fn(self) end
		idx.serialize = serialize_fn

		t.derived_serialize = true
	end,
	array = function(t, info)
		if t.derived_serialize then
			-- already derived, don't derive again
			return
		end

		local methods = t.methods

		local function serialize_fn(self) end
		methods.serialize = serialize_fn

		t.derived_serialize = true
	end,
}
