local traits = require "traits"
local pretty_printer = require "pretty-printer"

---@class (exact) Deriver
---@field record fun(t: RecordType, info: RecordDeriveInfo, override_pretty: fun(RecordType, PrettyPrint, ...), ...)
---@field enum fun(t: EnumType, info: EnumDeriveInfo, override_pretty: { [string]: fun(EnumType, PrettyPrint, ...) }, ...)

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

---@type Deriver
local eq = {
	record = function(t, info)
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
		if not compiled then
			error(message)
		end
		local eq_fn = compiled(eq_memoizer)
		t.__eq = eq_fn
	end,
	enum = function(t, info)
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
				local vparams = vinfo.params
				local checks = {}
				for i, param in ipairs(vparams) do
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
		if not compiled then
			error(message)
		end
		local eq_fn = compiled(eq_memoizer)
		t.__eq = eq_fn
	end,
}

---@type Deriver
local is = {
	record = function()
		error("can't derive :is() for a record type")
	end,
	enum = function(t, info)
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
			if not compiled then
				error(message)
			end
			idx["is_" .. vname] = compiled()
		end
	end,
}

---@type Deriver
local unwrap = {
	record = function(t, info)
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
		if not compiled then
			error(message)
		end
		idx["unwrap_" .. kind] = compiled()
	end,
	enum = function(t, info)
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
				local vparams = vinfo.params
				local returns = {}
				for i, param in ipairs(vparams) do
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
			if not compiled then
				error(message)
			end
			idx["unwrap_" .. vname] = compiled()
		end
	end,
}

---@type Deriver
local as = {
	record = function()
		error("can't derive :as() for a record type")
	end,
	enum = function(t, info)
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
				local vparams = vinfo.params
				local returns = { "true" }
				for i, param in ipairs(vparams) do
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
			if not compiled then
				error(message)
			end
			idx["as_" .. vname] = compiled()
		end
	end,
}

---@param info RecordDeriveInfo
---@return fun(self: Type, pp: PrettyPrint, ...)
local function record_pretty_printable_trait(info)
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

	derive_print("derive pretty_printable_trait chunk: " .. kind)
	derive_print("###")
	derive_print(chunk)
	derive_print("###")

	local compiled, message = load(chunk, "derive-pretty_printable_trait", "t")
	if not compiled then
		print(chunk)
		error(message)
	end
	return compiled()
end

---@type Deriver
local pretty_print = {
	record = function(t, info, override_pretty)
		local pretty_printable_print = record_pretty_printable_trait(info)
		local pretty_print = override_pretty or pretty_printable_print
		local default_print = pretty_printable_print

		traits.pretty_print:implement_on(t, { pretty_print = pretty_print, default_print = default_print })

		-- must be added here, instead of earlier in terms-gen, otherwise a type that doesn't derive
		-- pretty_print will cause pretty_print to call __tostring and loop until stack overflow
		t.__tostring = pretty_printer.pretty_print
	end,
	enum = function(t, info, override_pretty)
		local name = info.name
		local variants = info.variants

		local variant_pretty_printers = {}
		local variant_default_printers = {}
		for _, vname in ipairs(variants) do
			local vkind = name .. "." .. vname
			local vdata = variants[vname]
			local vtype = vdata.type
			local vinfo = vdata.info
			local override_pretty_v = override_pretty and override_pretty[vname]
			local variant_pretty_printable_print
			if vtype == EnumDeriveInfoVariantKind.Record then
				---@cast vinfo RecordDeriveInfo
				variant_pretty_printable_print = record_pretty_printable_trait(vinfo)
			elseif vtype == EnumDeriveInfoVariantKind.Unit then
				variant_pretty_printable_print = function(self, pp)
					pp:unit(self.kind)
				end
			else
				error("unknown variant type: " .. vtype)
			end
			variant_pretty_printers[vkind] = override_pretty_v or variant_pretty_printable_print
			variant_default_printers[vkind] = variant_pretty_printable_print
		end

		local function pretty_print(self, pp, ...)
			return variant_pretty_printers[self.kind](self, pp, ...)
		end
		local function default_print(self, pp, ...)
			return variant_default_printers[self.kind](self, pp, ...)
		end

		traits.pretty_print:implement_on(t, { pretty_print = pretty_print, default_print = default_print })

		-- must be added here, instead of earlier in terms-gen, otherwise a type that
		-- doesn't derive pretty_print will cause pretty_print to loop __tostring forever
		t.__tostring = pretty_printer.pretty_print
	end,
}

---@type Deriver
local diff = {
	record = function(t, info)
		local params = info.params
		local params_types = info.params_types

		local function diff_fn(left, right)
			print("diffing param kind: " .. left.kind)
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
			local diff_params_types = {}
			for i, param in ipairs(params) do
				if left[param] ~= right[param] then
					n = n + 1
					diff_params[n] = param
					diff_params_types[n] = param_types[i]
				end
			end
			if n == 0 then
				print("no difference")
				print("stopping diff")
				return
			elseif n == 1 then
				local d = diff_params[1]
				local dt = diff_params_types[1]
				print("difference in param: " .. d)
				local diff_impl = traits.diff:get(dt)
				if diff_impl then
					-- tail call
					return diff_impl.diff(left[d], right[d])
				else
					print("stopping diff (missing diff impl)")
					print("type:", dt)
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

		traits.diff:implement_on(t, { diff = diff_fn })
	end,
	enum = function(t, info)
		local name = info.name
		local variants = info.variants

		local variants_checks = {}
		for _, vname in ipairs(variants) do
			local vkind = name .. "." .. vname
			local vdata = variants[vname]
			local vtype = vdata.type
			local vinfo = vdata.info
			local vcheck
			if vtype == EnumDeriveInfoVariantKind.Record then
				---@cast vinfo RecordDeriveInfo
				function vcheck(left, right)
					local vparams = vinfo.params
					local vparams_types = vinfo.params_types
					local n = 0
					local diff_params = {}
					local diff_params_types = {}
					for i, param in ipairs(vparams) do
						if left[param] ~= right[param] then
							n = n + 1
							diff_params[n] = param
							diff_params_types[n] = vparams_types[i]
						end
					end
					if n == 0 then
						print("no difference")
						print("stopping diff")
						return
					elseif n == 1 then
						local d = diff_params[1]
						local dt = diff_params_types[1]
						print("difference in param: " .. d)
						local diff_impl = traits.diff:get(dt)
						if diff_impl then
							-- tail call
							return diff_impl.diff(left[d], right[d])
						else
							print("stopping diff (missing diff impl)")
							print("type:", dt)
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
			elseif vtype == EnumDeriveInfoVariantKind.Unit then
				function vcheck()
					print("no difference")
					print("stopping diff")
				end
			else
				error("unknown variant type: " .. vtype)
			end
			variants_checks[vkind] = vcheck
		end

		local function diff_fn(left, right)
			print("diffing enum kind: " .. left.kind)
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

		traits.diff:implement_on(t, { diff = diff_fn })
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
			if not compiled then
				error(message)
			end
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
	trait_method = trait_method,
}
