local derive_print = function(...) end -- can make this call derive_print(...) if you want to debug

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
			local vkind = name .. "_" .. vname
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

local is = {
	enum = function(t, info)
		local idx = t.__index or {}
		t.__index = idx
		local name = info.name
		local variants = info.variants

		for n, vname in ipairs(variants) do
			local vkind = name .. "_" .. vname
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
}

local function pretty_print_or_tostring(v, prefix)
	if type(v) == "string" then
		return string.format("%q", v)
	end
	if type(v) == "table" and v.pretty_print then
		return v:pretty_print(prefix)
	end
	return tostring(v)
end

local function record_pretty_printer(info)
	local kind = info.kind
	local params = info.params

	local prints = {}
	local lbracket, rbracket = "(", ")"
	local end_spacing = ""
	if #params == 0 then
	elseif #params == 1 then
		prints[1] = string.format(
			-- [[result = result .. %q .. ' = ' .. pretty_print_or_tostring(self[%q], np)]],
			[[result = result .. pretty_print_or_tostring(self[%q], np)]],
			params[1],
			params[1]
		)
	else
		end_spacing = [[.. "\n" .. prefix]]
		lbracket, rbracket = "{", "}"
		for i, param in ipairs(params) do
			prints[i] = string.format(
				[[result = result .. "\n" .. np .. %q .. ' = ' .. pretty_print_or_tostring(self[%q], np)]],
				param,
				param
			)
		end
	end
	local all_prints = table.concat(prints, "\n  ")
	local chunk = string.format(
		[[
local pretty_print_or_tostring = ...
return function(self, prefix)
prefix = prefix or ''
local np = prefix .. ' '
local result = %q .. %q
%s
result = result %s .. %q
return result
end
]],
		info.kind,
		lbracket,
		all_prints,
		end_spacing,
		rbracket
	)

	local compiled, message = load(chunk, "derive-pretty_print_record", "t")
	if not compiled then
		print(chunk)
	end
	assert(compiled, message)
	return compiled(pretty_print_or_tostring)
end

local pretty_print = {
	record = function(t, info)
		local idx = t.__index or {}
		t.__index = idx
		idx["pretty_print"] = record_pretty_printer(info)
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
			local vkind = name .. "_" .. vname
			local vdata = variants[vname]
			local vtype = vdata.type
			local vinfo = vdata.info
			if vtype == "record" then
				variant_printers[vkind] = record_pretty_printer(vinfo)
			elseif vtype == "unit" then
				variant_printers[vkind] = function(self)
					return self.kind
				end
			else
				error("unknown variant type: " .. vtype)
			end
		end

		local chunk = [[
      local variant_printers = ...
      return function(self, prefix)
        return variant_printers[self.kind](self, prefix)
      end
    ]]

		derive_print("derive pretty_print: enum chunk: " .. name)
		derive_print("###")
		derive_print(chunk)
		derive_print("###")

		local compiled, message = load(chunk, "derive-pretty_print_enum", "t")
		assert(compiled, message)
		idx["pretty_print"] = compiled(variant_printers)
		if not t["__tostring"] then
			t["__tostring"] = idx["pretty_print"]
		end
	end,
}

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
			local vkind = name .. "_" .. vname
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

local as = {
	enum = function(t, info)
		t:derive(unwrap)
		local idx = t.__index
		local name = info.name
		local variants = info.variants

		for n, vname in ipairs(variants) do
			local vkind = name .. "_" .. vname
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
				local vkind = name .. "_" .. vname
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
