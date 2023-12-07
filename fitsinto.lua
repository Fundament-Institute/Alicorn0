local terms = require "./terms"
local value = terms.value

local fitsinto
-- indexed by kind x kind
local fitsinto_comparers = {}

local function add_comparer(ka, kb, comparer)
	fitsinto_comparers[ka] = fitsinto_comparers[kb] or {}
	fitsinto_comparers[ka][kb] = comparer
end

local fitsinto_fail_mt = {
	__tostring = function(self)
		local message = self.message
		if type(message) == "table" then
			message = table.concat(message, "")
		end
		if self.cause then
			return message .. "." .. tostring(self.cause)
		end
		return message
	end,
}
local function fitsinto_fail(message, cause)
	if not cause and type(message) == "string" then
		if not message then
			error "missing error message for fitsinto_fail"
		end
		return message
	end
	return setmetatable({
		message = message,
		cause = cause,
	}, fitsinto_fail_mt)
end

local function always_fits_comparer(a, b)
	return true
end

-- prim types
for _, prim_type in ipairs({
	value.prim_number_type,
	value.prim_string_type,
	value.prim_bool_type,
}) do
	add_comparer(prim_type.kind, prim_type.kind, always_fits_comparer)
end

-- TODO: value.pi
-- TODO: value.tuple_type

-- types of types
add_comparer(value.prim_type_type.kind, value.prim_type_type.kind, always_fits_comparer)
add_comparer("value.pi", "value.pi", function(a, b)
	if not a:is_pi() and b:is_pi() then
		error "both arguments must be pis"
	end
	if a == b then
		return true
	end
	local ok, err
	ok, err = fitsinto(a.param_type, b.param_type)
	if not ok then
		return false, fitsinto_fail("param_type", err)
	end
	local avis = a.param_info.visibility.visibility
	local bvis = b.param_info.visibility.visibility
	if avis ~= bvis and avis ~= terms.visibility.implicit then
		return false, fitsinto_fail("param_info")
	end

	ok, err = fitsinto(a.param_info, b.param_info)
	if not ok then
		return false, fitsinto_fail("param_info", err)
	end

	local apurity = a.result_info.purity
	local bpurity = b.result_info.purity
	if apurity ~= bpurity then
		return false, fitsinto_fail("result_info")
	end

	ok, err = fitsinto(b.result_type, a.result_type)
	if not ok then
		return false, fitsinto_fail("result_type", err)
	end
	return true
end)

for _, type_of_type in ipairs({
	value.prim_type_type,
}) do
	add_comparer(type_of_type.kind, value.star(0).kind, always_fits_comparer)
end

add_comparer(value.star(0).kind, value.star(0).kind, function(a, b)
	if a.level > b.level then
		return false, "a.level > b.level"
	end
	return true
end)

local function quantities_fitsinto(qa, qb)
	if qa == qb or qa == terms.quantity.unrestricted or qb == terms.quantity.erased then
		return true
	end
	return false, qa.kind .. " doesn't fit into " .. qb.kind
end

function fitsinto(a, b)
	if not a:is_qtype() then
		print(a)
		error("fitsinto given value a which isn't a qtype " .. a.kind)
	end
	if not b:is_qtype() then
		print(b)
		error("fitsinto given value b which isn't a qtype " .. b.kind)
	end

	local qa, tya = a:unwrap_qtype()
	local qb, tyb = b:unwrap_qtype()

	if not fitsinto_comparers[tya.kind] then
		error("fitsinto given value a which isn't a type or NYI " .. tya.kind)
	elseif not fitsinto_comparers[tyb.kind] then
		error("fitsinto given value b which isn't a type or NYI " .. tyb.kind)
	end

	local ok, err = quantities_fitsinto(qa.quantity, qb.quantity)
	if not ok then
		return false, ".quantity " .. err
	end

	local comparer = (fitsinto_comparers[tya.kind] or {})[tyb.kind]
	if not comparer then
		return false, "no comparer for " .. tya.kind .. " with " .. tyb.kind
	end

	ok, err = comparer(tya, tyb)
	if not ok then
		return false, ".value" .. err
	end
	return true
end

return {
	fitsinto = fitsinto,
}
