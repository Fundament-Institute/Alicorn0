local traits = require './traits'
local terms = require './terms'
local gen = require './terms-generators'
local evaluator = require './evaluator'

local fitsinto = evaluator.fitsinto

local values = terms.value
local function test()
	local a = values.quantity(terms.quantity.unrestricted)
	local b = values.quantity(terms.quantity.erased)
	assert(fitsinto(a, a))
	assert(fitsinto(b, b))
	assert(fitsinto(a, b))
	assert(not fitsinto(b, a))
end

test()

