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
local serializer_deriver = {
	enum = function(t, info, override_pretty, ...)
		t.__save_term = function() end
	end,
}
