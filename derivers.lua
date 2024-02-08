---@alias RecordDeriveInfo { kind: string, params: string[], params_types: Type[] }
---@alias UnitDeriveInfo { kind: string }
---@alias EnumDeriveInfo { name: string, variants: { [number]: string, [string]: { type: string, info: RecordDeriveInfo | UnitDeriveInfo } } }

---@class (exact) Deriver
---@field record fun(t: Record, info: RecordDeriveInfo)
---@field enum fun(t: Enum, info: EnumDeriveInfo)

local derive_print = function(...) end -- can make this call derive_print(...) if you want to debug

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
		local chunk = "return function(left, right) return " .. all_checks .. " end"

		derive_print("derive eq: record chunk: " .. kind)
		derive_print("###")
		derive_print(chunk)
		derive_print("###")

		local compiled, message = load(chunk, "derive-eq_record", "t")
		assert(compiled, message)
		local eq_fn = compiled()
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
			if vtype == "record" then
				local checks = {}
				for i, param in ipairs(vinfo.params) do
					checks[i] = string.format("left[%q] == right[%q]", param, param)
				end
				all_checks = table.concat(checks, " and ")
			elseif vtype == "unit" then
				all_checks = "true"
			else
				error("unknown variant type: " .. vtype)
			end
			local entry = string.format("[%q] = function(left, right) return %s end", vkind, all_checks)
			variants_checks[n] = entry
		end
		local all_variants_checks = "{\n  " .. table.concat(variants_checks, ",\n  ") .. "\n}"
		local define_all_variants_checks = "local all_variants_checks = " .. all_variants_checks

		local kind_check_expression = "left.kind == right.kind"
		local variant_check_expression = "all_variants_checks[left.kind](left, right)"
		local check_expression = kind_check_expression .. " and " .. variant_check_expression
		local check_function = "function(left, right) return " .. check_expression .. " end"
		local chunk = define_all_variants_checks .. "\nreturn " .. check_function

		derive_print("derive eq: enum chunk: " .. name)
		derive_print("###")
		derive_print(chunk)
		derive_print("###")

		local compiled, message = load(chunk, "derive-eq_enum", "t")
		assert(compiled, message)
		local eq_fn = compiled()
		t.__eq = eq_fn
	end,
}

---@type Deriver
local is = {
	enum = function(t, info)
		local idx = t.__index or {}
		t.__index = idx
		local name = info.name
		local variants = info.variants

		for n, vname in ipairs(variants) do
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
	end,
	record = function(t, info) end,
}

local function record_prettyprintable_trait(info)
	local kind = info.kind
	local params = info.params

	local all_fields = {}
	for _, param in ipairs(params) do
		all_fields[#all_fields + 1] = string.format("{ %q, self[%q] },", param, param)
	end
	local chunk = string.format(
		[[
return function(self, pp)
	pp:record(%q, {
		%s
	})
end
]],
		info.kind,
		table.concat(all_fields, "\n\t\t")
	)

	local compiled, message = load(chunk, "derive-prettyprintable_trait", "t")
	if not compiled then
		print(chunk)
	end
	assert(compiled, message)
	return compiled()
end

---@type Deriver
local pretty_print = {
	record = function(t, info)
		local idx = t.__index or {}
		t.__index = idx
		local prettyprintable = require("./pretty-printer").prettyprintable
		local override_pretty = t.override_pretty
		if override_pretty then
			prettyprintable:implement_on(t, { print = override_pretty })
		else
			local prettyprintable_print = record_prettyprintable_trait(info)
			prettyprintable:implement_on(t, { print = prettyprintable_print })
		end
		idx["pretty_print"] = function(self)
			local pp = require("./pretty-printer").PrettyPrint.new()
			prettyprintable_print(self, pp)
			return tostring(pp)
		end

		if not t["__tostring"] then
			t["__tostring"] = idx["pretty_print"]
		end
		if not t["__tostring"] then
			t["__tostring"] = idx["pretty_print"]
		end
	end,
	enum = function(t, info)
		local idx = t.__index or {}
		t.__index = idx
		local name = info.name
		local variants = info.variants

		local variant_printers = {}
		for n, vname in ipairs(variants) do
			local vkind = name .. "." .. vname
			local vdata = variants[vname]
			local vtype = vdata.type
			local vinfo = vdata.info
			local override_pretty = t.override_pretty and t.override_pretty[vname]
			if override_pretty then
				variant_printers[vkind] = override_pretty
			elseif vtype == "record" then
				variant_printers[vkind] = record_prettyprintable_trait(vinfo)
			elseif vtype == "unit" then
				variant_printers[vkind] = function(self, printer)
					return printer:unit(self.kind)
				end
			else
				error("unknown variant type: " .. vtype)
			end
		end

		local chunk = [[
      local variant_printers = ...
      return function(self, prefix)
		if not variant_printers[self.kind] then
			error("missing variant_printer for" .. self.kind)
		end
        return variant_printers[self.kind](self, prefix)
      end
    ]]

		derive_print("derive pretty_print: enum chunk: " .. name)
		derive_print("###")
		derive_print(chunk)
		derive_print("###")

		local compiled, message = load(chunk, "derive-pretty_print_enum", "t")
		assert(compiled, message)
		local prettyprintable_print = compiled(variant_printers)

		local prettyprintable = require("./pretty-printer").prettyprintable
		prettyprintable:implement_on(t, { print = prettyprintable_print })
		idx["pretty_print"] = function(self)
			local pp = require("./pretty-printer").PrettyPrint.new()
			prettyprintable_print(self, pp)
			return tostring(pp)
		end

		if not t["__tostring"] then
			t["__tostring"] = idx["pretty_print"]
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
		local chunk = "return function(self) return " .. all_returns .. " end"

		derive_print("derive unwrap: record chunk: " .. kind)
		derive_print("###")
		derive_print(chunk)
		derive_print("###")

		local compiled, message = load(chunk, "derive-unwrap_record", "t")
		assert(compiled, message)
		idx["unwrap_" .. kind] = compiled()
	end,
	enum = function(t, info)
		t:derive(is)
		local idx = t.__index
		local name = info.name
		local variants = info.variants

		for n, vname in ipairs(variants) do
			local vkind = name .. "." .. vname
			local vdata = variants[vname]
			local vtype = vdata.type
			local vinfo = vdata.info
			local all_returns
			if vtype == "record" then
				local returns = {}
				for i, param in ipairs(vinfo.params) do
					returns[i] = string.format("self[%q]", param)
				end
				all_returns = table.concat(returns, ", ")
			elseif vtype == "unit" then
				all_returns = ""
			else
				error("unknown variant type: " .. vtype)
			end
			local error_message = "unwrap failed: unwrapping for a " .. vkind .. " but found a "
			local error_statement = string.format("error(%q .. self.kind)", error_message)
			local chunk = "return function(self) if self:is_"
				.. vname
				.. "() then return "
				.. all_returns
				.. " else "
				.. error_statement
				.. " end end"

			derive_print("derive unwrap: enum chunk: " .. vkind)
			derive_print("###")
			derive_print(chunk)
			derive_print("###")

			local compiled, message = load(chunk, "derive-unwrap_enum", "t")
			assert(compiled, message)
			idx["unwrap_" .. vname] = compiled()
		end
	end,
}

---@type Deriver
local as = {
	enum = function(t, info)
		t:derive(unwrap)
		local idx = t.__index
		local name = info.name
		local variants = info.variants

		for n, vname in ipairs(variants) do
			local vkind = name .. "." .. vname
			local chunk = "return function(self) return pcall(function() return self:unwrap_" .. vname .. "() end) end"

			derive_print("derive as: enum chunk: " .. vkind)
			derive_print("###")
			derive_print(chunk)
			derive_print("###")

			local compiled, message = load(chunk, "derive-as_enum", "t")
			assert(compiled, message)
			idx["as_" .. vname] = compiled()
		end
	end,
	record = function(t, info) end,
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
			for n, vname in ipairs(variants) do
				local vkind = name .. "." .. vname
				local vdata = variants[vname]
				local vtype = vdata.type
				local vinfo = vdata.info
				if specializations[vname] then
					variant_impls[vkind] = specializations[vname]
				elseif vtype == "record" then
					variant_impls[vkind] = build_record_function(trait, t, vinfo)
				elseif vtype == "unit" then
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
				end
			]]

			local compiled, message = load(chunk, "derive-pretty_print_enum", "t")
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
	eq = eq,
	is = is,
	unwrap = unwrap,
	as = as,
	pretty_print = pretty_print,
	trait_method = trait_method,
}
