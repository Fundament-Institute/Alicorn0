local terms = require "terms"
local value = terms.value

-- indexed by kind x kind
local fitsinto_comparers = {}

local function add_comparer(ka, kb, comparer)
	fitsinto_comparers[ka] = fitsinto_comparers[kb] or {}
	fitsinto_comparers[ka][kb] = comparer
end

for _, basic_type in ipairs({ value.prim_number_type, value.prim_string_type, value.prim_bool_type, value.string_type }) do
	add_comparer(basic_type.kind, basic_type.kind, function(a, b)
		return a == b
	end)
end

local function quantities_fitsinto(qa, qb)
	return qa == qb or qa == terms.quantity.unrestricted or qb == terms.quantity.erased
end

local function fitsinto(a, b)
	if not (a:is_qtype() and b:is_qtype()) then
		error "fitsinto given value which isn't a qtype"
	end

	local qa, tya = a:unwrap_qtype()
	local qb, tyb = b:unwrap_qtype()

	if not fitsinto_comparers[tya.kind] or not fitsinto_comparers[tyb.kind] then
		error "fitsinto given value which isn't a type or NYI"
	end

	local ok, err = quantities_fitsinto(qa:unwrap_quantity(), qb:unwrap_quantity())
	if not ok then
		return false, ".quantity " .. err
	end

	local comparer = (fitsinto_comparers[tya.kind] or {})[tyb.kind]
	if not comparer then
		return false, "no comparer for " .. tya.kind .. " with " .. tyb.kind
	end

	ok, err = comparer(a, b)
	if not ok then
		return false, ".value" .. err
	end
	return true
end

return {
	fitsinto = fitsinto,
}
