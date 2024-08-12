---@class (exact) Deriver
---@field record fun(t: RecordType, info: RecordDeriveInfo, override_pretty: fun(RecordType, PrettyPrint, ...), ...)
---@field enum fun(t: EnumType, info: EnumDeriveInfo, override_pretty: { [string]: fun(EnumType, PrettyPrint, ...) }, ...)
---@field foreign fun(t: ForeignType, info: ForeignDeriveInfo, ...)
---@field map fun(t: MapType, info: MapDeriveInfo, ...)
---@field set fun(t: SetType, info: SetDeriveInfo, ...)
---@field array fun(t: ArrayType, info: ArrayDeriveInfo, ...)

---@class (exact) RecordDeriveInfo
---@field kind string
---@field params string[]
---@field params_types Type[]

---@class (exact) UnitDeriveInfo
---@field kind string

---@class EnumDeriveInfoVariantKindContainer
local EnumDeriveInfoVariantKind = --[[@enum EnumDeriveInfoVariantKind]]
	{
		Record = "Record",
		Unit = "Unit",
	}

---@class (exact) EnumDeriveInfoVariant
---@field type EnumDeriveInfoVariantKind
---@field info RecordDeriveInfo | UnitDeriveInfo

---@class (exact) EnumDeriveInfo
---@field name string
---@field variants { [integer]: string, [string]: EnumDeriveInfoVariant }

---@class (exact) ForeignDeriveInfo
---@field value_check ValueCheckFn
---@field lsp_type string

---@class (exact) MapDeriveInfo
---@field key_type Type
---@field value_type Type

---@class (exact) SetDeriveInfo
---@field key_type Type

---@class (exact) ArrayDeriveInfo
---@field value_type Type

local derive_print = function(...) end -- can make this call print(...) if you want to debug

local memo_meta = { __mode = "k" }
local function make_memo_table()
	return setmetatable({}, memo_meta)
end
local eq_memoizer = { memo = make_memo_table() }
function eq_memoizer:check(a, b)
	local memoa = self.memo[a]
	if memoa then
		return memoa[b]
	end
end
function eq_memoizer:set(a, b)
	if not self.memo[a] then
		self.memo[a] = make_memo_table()
	end
	self.memo[a][b] = true
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

---@type Deriver
local eq = {
	record = function(t, info)
		if t.derived_eq then
			-- already derived, don't derive again
			return
		end

		local kind = info.kind
		local params = info.params

		local checks = {}
		for i, param in ipairs(params) do
			checks[i] = string.format("left[%q] == right[%q]", param, param)
		end
		local all_checks = table.concat(checks, " and ")

		local chunk = [[
local eq_memoizer = ...
return function(left, right)
	if getmetatable(left) ~= getmetatable(right) then
		return false
	end
	if eq_memoizer:check(left, right) then
		return true
	end
	if %s then
		eq_memoizer:set(left, right)
		return true
	end
	return false
end]]
		chunk = chunk:format(all_checks)

		derive_print("derive eq: record chunk: " .. kind)
		derive_print("###")
		derive_print(chunk)
		derive_print("###")

		local compiled, message = load(chunk, "derive-eq_record", "t")
		assert(compiled, message)
		local eq_fn = compiled(eq_memoizer)
		t.__eq = eq_fn

		t.derived_eq = true
	end,
	enum = function(t, info)
		if t.derived_eq then
			-- already derived, don't derive again
			return
		end

		local name = info.name
		local variants = info.variants

		local variants_checks = {}
		for n, vname in ipairs(variants) do
			local vkind = name .. "." .. vname
			local vdata = variants[vname]
			local vtype = vdata.type
			local vinfo = vdata.info
			local all_checks
			if vtype == EnumDeriveInfoVariantKind.Record then
				local checks = {}
				for i, param in ipairs(vinfo.params) do
					checks[i] = string.format("left[%q] == right[%q]", param, param)
				end
				all_checks = table.concat(checks, " and ")
			elseif vtype == EnumDeriveInfoVariantKind.Unit then
				all_checks = "true"
			else
				error("unknown variant type: " .. vtype)
			end
			variants_checks[n] = string.format("[%q] = function(left, right) return %s end", vkind, all_checks)
		end
		local all_variants_checks = "	" .. table.concat(variants_checks, ",\n	") .. "\n"

		local chunk = [[
local eq_memoizer = ...
local all_variants_checks = {
%s
}
return function(left, right)
	if getmetatable(left) ~= getmetatable(right) then
		return false
	end
	if eq_memoizer:check(left, right) then
		return true
	end
	if left.kind == right.kind and all_variants_checks[left.kind](left, right) then
		eq_memoizer:set(left, right)
		return true
	end
	return false
end]]
		chunk = chunk:format(all_variants_checks)

		derive_print("derive eq: enum chunk: " .. name)
		derive_print("###")
		derive_print(chunk)
		derive_print("###")

		local compiled, message = load(chunk, "derive-eq_enum", "t")
		assert(compiled, message)
		local eq_fn = compiled(eq_memoizer)
		t.__eq = eq_fn

		t.derived_eq = true
	end,
	foreign = function()
		error("can't derive :eq() for a foreign type")
	end,
	map = function()
		error("can't derive :eq() for a map type")
	end,
	set = function()
		error("can't derive :eq() for a set type")
	end,
	array = function(t, info)
		if t.derived_eq then
			-- already derived, don't derive again
			return
		end

		t.__eq = array_eq_fn

		t.derived_eq = true
	end,
}

---@type Deriver
local is = {
	record = function()
		error("can't derive :is() for a record type")
	end,
	enum = function(t, info)
		if t.derived_is then
			-- already derived, don't derive again
			return
		end

		local idx = t.__index or {}
		t.__index = idx
		local name = info.name
		local variants = info.variants

		for _, vname in ipairs(variants) do
			local vkind = name .. "." .. vname
			local chunk = string.format("return function(self) return self.kind == %q end", vkind)

			derive_print("derive is: enum chunk: " .. vkind)
			derive_print("###")
			derive_print(chunk)
			derive_print("###")

			local compiled, message = load(chunk, "derive-is_enum", "t")
			assert(compiled, message)
			idx["is_" .. vname] = compiled()
		end

		t.derived_is = true
	end,
	foreign = function()
		error("can't derive :is() for a foreign type")
	end,
	map = function()
		error("can't derive :is() for a map type")
	end,
	set = function()
		error("can't derive :is() for a set type")
	end,
	array = function()
		error("can't derive :is() for an array type")
	end,
}

---@type Deriver
local unwrap = {
	record = function(t, info)
		if t.derived_unwrap then
			-- already derived, don't derive again
			return
		end

		local idx = t.__index or {}
		t.__index = idx
		local kind = info.kind
		local params = info.params

		local returns = {}
		for i, param in ipairs(params) do
			returns[i] = string.format("self[%q]", param)
		end
		local all_returns = table.concat(returns, ", ")

		local chunk = string.format("return function(self) return %s end", all_returns)

		derive_print("derive unwrap: record chunk: " .. kind)
		derive_print("###")
		derive_print(chunk)
		derive_print("###")

		local compiled, message = load(chunk, "derive-unwrap_record", "t")
		assert(compiled, message)
		idx["unwrap_" .. kind] = compiled()
		t.derived_unwrap = true
	end,
	enum = function(t, info)
		if t.derived_unwrap then
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
			local all_returns
			if vtype == EnumDeriveInfoVariantKind.Record then
				local returns = {}
				for i, param in ipairs(vinfo.params) do
					returns[i] = string.format("self[%q]", param)
				end
				all_returns = table.concat(returns, ", ")
			elseif vtype == EnumDeriveInfoVariantKind.Unit then
				all_returns = ""
			else
				error("unknown variant type: " .. vtype)
			end

			local chunk = [[
return function(self)
	if self.kind == %q then
		return %s
	else
		error("unwrap failed: unwrapping for a %s but found a " .. self.kind)
	end
end]]
			chunk = chunk:format(vkind, all_returns, vkind)

			derive_print("derive unwrap: enum chunk: " .. vkind)
			derive_print("###")
			derive_print(chunk)
			derive_print("###")

			local compiled, message = load(chunk, "derive-unwrap_enum", "t")
			assert(compiled, message)
			idx["unwrap_" .. vname] = compiled()
		end

		t.derived_unwrap = true
	end,
	foreign = function()
		error("can't derive :unwrap() for a foreign type")
	end,
	map = function()
		error("can't derive :unwrap() for a map type")
	end,
	set = function()
		error("can't derive :unwrap() for a set type")
	end,
	array = function()
		error("can't derive :unwrap() for an array type")
	end,
}

---@type Deriver
local as = {
	record = function()
		error("can't derive :as() for a record type")
	end,
	enum = function(t, info)
		if t.derived_as then
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
			local all_returns
			if vtype == EnumDeriveInfoVariantKind.Record then
				local returns = { "true" }
				for i, param in ipairs(vinfo.params) do
					returns[i + 1] = string.format("self[%q]", param)
				end
				all_returns = table.concat(returns, ", ")
			elseif vtype == EnumDeriveInfoVariantKind.Unit then
				all_returns = "true"
			else
				error("unknown variant type: " .. vtype)
			end

			local chunk = [[
return function(self)
	if self.kind == %q then
		return %s
	else
		return false
	end
end]]
			chunk = chunk:format(vkind, all_returns)

			derive_print("derive as: enum chunk: " .. vkind)
			derive_print("###")
			derive_print(chunk)
			derive_print("###")

			local compiled, message = load(chunk, "derive-as_enum", "t")
			assert(compiled, message)
			idx["as_" .. vname] = compiled()
		end

		t.derived_as = true
	end,
	foreign = function()
		error("can't derive :as() for a foreign type")
	end,
	map = function()
		error("can't derive :as() for a map type")
	end,
	set = function()
		error("can't derive :as() for a set type")
	end,
	array = function()
		error("can't derive :as() for an array type")
	end,
}

---@param info RecordDeriveInfo
---@return fun(self: Type, pp: PrettyPrint, ...)
local function record_prettyprintable_trait(info)
	local kind = info.kind
	local params = info.params

	local fields = {}
	for i, param in ipairs(params) do
		fields[i] = string.format("{ %q, self[%q] }", param, param)
	end
	local all_fields = "		" .. table.concat(fields, ",\n		") .. "\n"

	local chunk = [[
return function(self, pp, ...)
	pp:record(%q, {
%s
	}, ...)
end]]
	chunk = chunk:format(kind, all_fields)

	derive_print("derive prettyprintable_trait chunk: " .. kind)
	derive_print("###")
	derive_print(chunk)
	derive_print("###")

	local compiled, message = load(chunk, "derive-prettyprintable_trait", "t")
	if not compiled then
		print(chunk)
	end
	assert(compiled, message)
	return compiled()
end

local function map_prettyprintable_trait(self, pp, ...)
	return pp:table(self._map, ...)
end

local function set_prettyprintable_trait(self, pp, ...)
	return pp:table(self._set, ...)
end

local function array_prettyprintable_trait(self, pp, ...)
	return pp:array(self.array, ...)
end

local pretty_printer = require "./pretty-printer"
local PrettyPrint = pretty_printer.PrettyPrint
local prettyprintable = pretty_printer.prettyprintable

---@type Deriver
local pretty_print = {
	record = function(t, info, override_pretty)
		if t.derived_pretty_print then
			-- already derived, don't derive again
			return
		end

		local idx = t.__index or {}
		t.__index = idx

		local prettyprintable_print = record_prettyprintable_trait(info)
		local function pretty(self, pp, ...)
			if override_pretty and not pp.force_default then
				override_pretty(self, pp, ...)
			else
				prettyprintable_print(self, pp, ...)
			end
		end

		prettyprintable:implement_on(t, { print = pretty })

		local function pretty_print(self, ...)
			local pp = PrettyPrint.new()
			pretty(self, pp, ...)
			return tostring(pp)
		end
		idx.pretty_print = pretty_print

		local function default_print(self, ...)
			local pp = PrettyPrint.new()
			pp.force_default = true
			pretty(self, pp, ...)
			return tostring(pp)
		end
		idx.default_print = default_print

		t.__tostring = pretty_print

		t.derived_pretty_print = true
	end,
	enum = function(t, info, override_pretty)
		if t.derived_pretty_print then
			-- already derived, don't derive again
			return
		end

		local idx = t.__index or {}
		t.__index = idx
		local name = info.name
		local variants = info.variants

		local variant_printers = {}
		for _, vname in ipairs(variants) do
			local vkind = name .. "." .. vname
			local vdata = variants[vname]
			local vtype = vdata.type
			local vinfo = vdata.info
			local override_pretty_v = override_pretty and override_pretty[vname]
			local variant_prettyprintable_print
			if vtype == EnumDeriveInfoVariantKind.Record then
				---@cast vinfo RecordDeriveInfo
				variant_prettyprintable_print = record_prettyprintable_trait(vinfo)
			elseif vtype == EnumDeriveInfoVariantKind.Unit then
				variant_prettyprintable_print = function(self, pp)
					pp:unit(self.kind)
				end
			else
				error("unknown variant type: " .. vtype)
			end
			variant_printers[vkind] = function(self, pp, ...)
				if override_pretty_v and not pp.force_default then
					override_pretty_v(self, pp, ...)
				else
					variant_prettyprintable_print(self, pp, ...)
				end
			end
		end

		local function prettyprintable_print(self, prefix, ...)
			return variant_printers[self.kind](self, prefix, ...)
		end

		prettyprintable:implement_on(t, { print = prettyprintable_print })

		local function pretty_print(self, ...)
			local pp = PrettyPrint.new()
			prettyprintable_print(self, pp, ...)
			return tostring(pp)
		end
		idx.pretty_print = pretty_print

		local function default_print(self, ...)
			local pp = PrettyPrint.new()
			pp.force_default = true
			prettyprintable_print(self, pp, ...)
			return tostring(pp)
		end
		idx.default_print = default_print

		t.__tostring = pretty_print

		t.derived_pretty_print = true
	end,
	foreign = function()
		error("can't derive :pretty_print() for a foreign type")
	end,
	map = function(t, info)
		if t.derived_pretty_print then
			-- already derived, don't derive again
			return
		end

		local idx = t.__index

		prettyprintable:implement_on(t, {
			print = map_prettyprintable_trait,
		})

		local function pretty_print(self, ...)
			local pp = PrettyPrint.new()
			map_prettyprintable_trait(self, pp, ...)
			return tostring(pp)
		end
		idx.pretty_print = pretty_print

		local function default_print(self, ...)
			local pp = PrettyPrint.new()
			pp.force_default = true
			map_prettyprintable_trait(self, pp, ...)
			return tostring(pp)
		end
		idx.default_print = default_print

		t.__tostring = pretty_print

		t.derived_pretty_print = true
	end,
	set = function(t, info)
		if t.derived_pretty_print then
			-- already derived, don't derive again
			return
		end

		local idx = t.__index

		prettyprintable:implement_on(t, {
			print = set_prettyprintable_trait,
		})

		local function pretty_print(self, ...)
			local pp = PrettyPrint.new()
			set_prettyprintable_trait(self, pp, ...)
			return tostring(pp)
		end
		idx.pretty_print = pretty_print

		local function default_print(self, ...)
			local pp = PrettyPrint.new()
			pp.force_default = true
			set_prettyprintable_trait(self, pp, ...)
			return tostring(pp)
		end
		idx.default_print = default_print

		t.__tostring = pretty_print

		t.derived_pretty_print = true
	end,
	array = function(t, info)
		if t.derived_pretty_print then
			-- already derived, don't derive again
			return
		end

		local methods = t.methods

		prettyprintable:implement_on(t, {
			print = array_prettyprintable_trait,
		})

		local function pretty_print(self, ...)
			local pp = PrettyPrint.new()
			array_prettyprintable_trait(self, pp, ...)
			return tostring(pp)
		end
		methods.pretty_print = pretty_print

		local function default_print(self, ...)
			local pp = PrettyPrint.new()
			pp.force_default = true
			array_prettyprintable_trait(self, pp, ...)
			return tostring(pp)
		end
		methods.default_print = default_print

		t.__tostring = pretty_print

		t.derived_pretty_print = true
	end,
}

---@type Deriver
local diff = {
	record = function(t, info)
		if t.derived_diff then
			-- already derived, don't derive again
			return
		end

		local idx = t.__index or {}
		t.__index = idx
		local kind = info.kind
		local params = info.params

		local function diff_fn(left, right)
			print("diffing...")
			print("kind: " .. left.kind)
			local rt = getmetatable(right)
			if t ~= rt then
				print("unequal types!")
				print(t)
				print(rt)
				print("stopping diff")
				return
			end
			if left.kind ~= right.kind then
				print("unequal kinds!")
				print(left.kind)
				print(right.kind)
				print("stopping diff")
				return
			end
			local n = 0
			local diff_params = {}
			for _, param in ipairs(params) do
				if left[param] ~= right[param] then
					n = n + 1
					diff_params[n] = param
				end
			end
			if n == 0 then
				print("no difference")
				print("stopping diff")
				return
			elseif n == 1 then
				local d = diff_params[1]
				print("difference in param: " .. d)
				if left[d].diff then
					-- tail call
					return left[d]:diff(right[d])
				else
					print("stopping diff (missing diff method)")
					return
				end
			else
				print("difference in multiple params:")
				for i = 1, n do
					print(diff_params[i])
				end
				print("stopping diff")
				return
			end
		end

		idx.diff = diff_fn
		t.derived_diff = true
	end,
	enum = function(t, info)
		if t.derived_diff then
			-- already derived, don't derive again
			return
		end

		local idx = t.__index or {}
		t.__index = idx
		local name = info.name
		local variants = info.variants

		local variants_checks = {}
		for _, vname in ipairs(variants) do
			local vkind = name .. "." .. vname
			local vdata = variants[vname]
			local vtype = vdata.type
			local vinfo = vdata.info
			variants_checks[vkind] = function(left, right)
				local n = 0
				local diff_params = {}
				for _, param in ipairs(vinfo.params) do
					if left[param] ~= right[param] then
						n = n + 1
						diff_params[n] = param
					end
				end
				if n == 0 then
					print("no difference")
					print("stopping diff")
					return
				elseif n == 1 then
					local d = diff_params[1]
					print("difference in param: " .. d)
					if left[d].diff then
						-- tail call
						return left[d]:diff(right[d])
					else
						print("stopping diff (missing diff method)")
						return
					end
				else
					print("difference in multiple params:")
					for i = 1, n do
						print(diff_params[i])
					end
					print("stopping diff")
					return
				end
			end
		end

		local function diff_fn(left, right)
			print("diffing...")
			print("kind: " .. left.kind)
			local rt = getmetatable(right)
			if t ~= rt then
				print("unequal types!")
				print(t)
				print(rt)
				print("stopping diff")
				return
			end
			if left.kind ~= right.kind then
				print("unequal kinds!")
				print(left.kind)
				print(right.kind)
				print("stopping diff")
				return
			end
			variants_checks[left.kind](left, right)
		end

		idx.diff = diff_fn
		t.derived_diff = true
	end,
	foreign = function()
		error("can't derive :diff() for a foreign type")
	end,
	map = function()
		error("can't derive :diff() for a map type")
	end,
	set = function()
		error("can't derive :diff() for a set type")
	end,
	array = function(t, info)
		if t.derived_diff then
			-- already derived, don't derive again
			return
		end

		local methods = t.methods

		local function diff_fn(left, right)
			print("diffing array...")
			print("value_type: " .. tostring(info.value_type))
			local rt = getmetatable(right)
			if t ~= rt then
				print("unequal types!")
				print(t)
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
				if left[d].diff then
					-- tail call
					return left[d]:diff(right[d])
				else
					print("stopping diff (missing diff method)")
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

		methods.diff = diff_fn
		t.derived_diff = true
	end,
}

---@type Deriver
local value_name = {
	record = function(t, info)
		if t.derived_value_name then
			-- already derived, don't derive again
			return
		end
		t.value_name = function()
			return info.kind
		end
		t.derived_value_name = true
	end,
	enum = function(t, info)
		if t.derived_value_name then
			-- already derived, don't derive again
			return
		end
		local name = info.name
		t.value_name = function()
			return name
		end
		t.derived_value_name = true
	end,
	foreign = function(t, info)
		if t.derived_value_name then
			-- already derived, don't derive again
			return
		end
		local lsp_type = info.lsp_type
		t.value_name = function()
			return lsp_type
		end
		t.derived_value_name = true
	end,
	-- TODO: augment all these with generics
	map = function(t, info)
		if t.derived_value_name then
			-- already derived, don't derive again
			return
		end
		t.value_name = function()
			return "MapValue"
			-- e.g. "MapValue<" .. info.key_type.value_name() .. ", " .. info.value_type.value_name() .. ">""
		end
		t.derived_value_name = true
	end,
	set = function(t, info)
		if t.derived_value_name then
			-- already derived, don't derive again
			return
		end
		t.value_name = function()
			return "SetValue"
		end
		t.derived_value_name = true
	end,
	array = function(t, info)
		if t.derived_value_name then
			-- already derived, don't derive again
			return
		end
		t.value_name = function()
			return "ArrayValue"
		end
		t.derived_value_name = true
	end,
}

-- build_record_function = (trait, info) -> function that implements the trait method
-- specializations - optional specialized implementations for particular variants
local function trait_method(trait, method, build_record_function, specializations)
	specializations = specializations or {}
	return {
		record = function(t, info)
			trait:implement_on(t, {
				[method] = build_record_function(trait, t, info),
			})
		end,
		enum = function(t, info)
			local name = info.name
			local variants = info.variants

			local variant_impls = {}
			for _, vname in ipairs(variants) do
				local vkind = name .. "." .. vname
				local vdata = variants[vname]
				local vtype = vdata.type
				local vinfo = vdata.info
				if specializations[vname] then
					variant_impls[vkind] = specializations[vname]
				elseif vtype == EnumDeriveInfoVariantKind.Record then
					variant_impls[vkind] = build_record_function(trait, t, vinfo)
				elseif vtype == EnumDeriveInfoVariantKind.Unit then
					variant_impls[vkind] = function(self, other)
						return self == other
					end
				else
					error("unknown variant type: " .. vtype)
				end
			end

			local chunk = [[
local variant_impls = ...
return function(self, other)
	return variant_impls[self.kind](self, other)
end]]

			derive_print("derive trait_method: enum chunk: " .. name)
			derive_print("###")
			derive_print(chunk)
			derive_print("###")

			local compiled, message = load(chunk, "derive-trait_method_enum", "t")
			assert(compiled, message)
			trait:implement_on(t, {
				[method] = compiled(variant_impls),
			})
		end,
	}
end

-- local typed = terms.inferrable_term.typed(terms.value.number_type, gen.declare_array(gen.builtin_number)(), terms.typed_term.literal(terms.value.number(1)))
-- p(typed)
-- p(getmetatable(typed))
-- p(terms.inferrable_term == getmetatable(typed))

return {
	EnumDeriveInfoVariantKind = EnumDeriveInfoVariantKind,
	eq = eq,
	is = is,
	unwrap = unwrap,
	as = as,
	pretty_print = pretty_print,
	diff = diff,
	value_name = value_name,
	trait_method = trait_method,
}
