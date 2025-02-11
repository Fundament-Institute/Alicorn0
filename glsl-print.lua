local internals_interface = require "internals-interface"
internals_interface.glsl_registry = {}
internals_interface.glsl_print = glsl_print

local traits = require "traits"

local function glsl_fallback(unknown, pp)
	pp:unit("/* wtf is this: ")
	pp:unit(tostring(unknown))
	pp:unit("*/")
end

local glsl_print_deriver = {
	record = function(t, info, glsl_variants)
		error("notimp")
	end,
	enum = function(t, info, glsl_variants)
		local name = info.name
		local variants = info.variants

		local variant_glsl_printers = {}
		for _, vname in ipairs(variants) do
			local vkind = name .. "." .. vname
			variant_glsl_printers[vkind] = glsl_variants[vname] or glsl_fallback
		end

		local function glsl_print(self, pp, ...)
			return variant_glsl_printers[self.kind](self, pp, ...)
		end

		traits.glsl_print:implement_on(t, { glsl_print = glsl_print })
	end,
}

local typed_term_glsl = {}

function typed_term_glsl:literal(pp)
	local literal_value = self:unwrap_literal()

	if not literal_value:is_host_value() then
		return glsl_fallback(self, pp)
	end
	local val = literal_value:unwrap_host_value()
	pp:any(val)
end

local function access_application(self, subject, index, pp, varnames)
	if index ~= 1 then
		return glsl_fallback(self, pp)
	end

	local f, arg = subject:unwrap_application()

	if not f:is_literal() or not f:unwrap_literal():is_host_value() then
		return glsl_fallback(self, pp)
	end
	local host_f = f:unwrap_literal():unwrap_host_value()

	local print_f = internals_interface.glsl_registry[host_f]
	if not print_f then
		return glsl_fallback(self, pp)
	end

	if not arg:is_host_tuple_cons() then
		return glsl_fallback(self, pp)
	end
	local elements = arg:unwrap_host_tuple_cons()

	pp:_enter()
	print_f(pp, varnames, elements:unpack())
	pp:_exit()
end

local function access_variable(self, subject, index, pp, varnames)
	local var_index, debug = subject:unwrap_bound_variable()

	local var = varnames[var_index]
	if not var then
		return glsl_fallback(self, pp)
	end

	local var_name = var[index]
	if not var_name then
		return glsl_fallback(self, pp)
	end

	pp:unit(var_name)
end

function typed_term_glsl:tuple_element_access(pp, varnames)
	local subject, index = self:unwrap_tuple_element_access()

	if subject:is_application() then
		return access_application(self, subject, index, pp, varnames)
	end
	if subject:is_bound_variable() then
		return access_variable(self, subject, index, pp, varnames)
	end
	return glsl_fallback(self, pp)
end

local function glsl_print(pp, unknown, ...)
	local ty = type(unknown)
	if ty == "number" then
		pp:unit(string.format("%f", unknown))
		return
	end
	if ty == "table" then
		if pp.depth and pp.depth > 50 then
			pp:unit("DEPTH LIMIT EXCEEDED")
			return
		end
		local mt = getmetatable(unknown)
		local via_trait = mt and traits.glsl_print:get(mt)
		if via_trait then
			via_trait.glsl_print(unknown, pp, ...)
			return
		end
		local reg_entry = mt and internals_interface.glsl_registry[mt]
		if reg_entry then
			reg_entry(pp, unknown, ...)
			return
		end
	end
	return glsl_fallback(unknown, pp)
end

return {
	glsl_print_deriver = glsl_print_deriver,
	typed_term_glsl = typed_term_glsl,
	glsl_print = glsl_print,
}
