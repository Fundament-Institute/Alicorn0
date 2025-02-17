-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>
---@class LuaTrait
---@field declare_method fun(self: LuaTrait, methodname: string)
---@field implement_on fun(self: LuaTrait, ty: Type, methods: { [string]: function })
---@field get fun(self: LuaTrait, ty: Type): { [string]: function }

local count_impls = 0

local trait_type_mt = {
	__index = {
		declare_method = function(self, methodname)
			if self.methods[methodname] then
				error("trait " .. self.name .. " method " .. methodname .. " is already declared")
			end
			self.methods[methodname] = true
		end,
		implement_on = function(self, ty, methods)
			count_impls = count_impls + 1
			--if count_impls == 10000 then error "too many impls" end
			if type(ty) ~= "table" then
				error("trying to implement on something that isn't a type")
			end
			if self.impls[ty] then
				error("trait " .. self.name .. " already implemented on type " .. tostring(ty))
			end
			local implemented_methods = {}
			for k in pairs(self.methods) do
				implemented_methods[k] = methods[k]
					or error(
						"missing method " .. k .. " implementing trait " .. self.name .. " on type " .. tostring(ty)
					)
			end
			self.impls[ty] = implemented_methods
		end,
		get = function(self, ty)
			return self.impls[ty] or nil --error("trait " .. self.name .. " not implemented on type " .. tostring(ty))
		end,
	},
}

---@param name string
---@return LuaTrait
local function declare_trait(name)
	return setmetatable({ name = name, methods = {}, impls = {} }, trait_type_mt)
end

-- this trait system is not powerful enough to represent is/unwrap/as
-- but those are exclusive to records and enums, so it's ok
-- eq is not declared as a trait because we'll never use it via traits

local pretty_print = declare_trait("pretty_print")
pretty_print:declare_method("pretty_print")
pretty_print:declare_method("default_print")

local diff = declare_trait("diff")
diff:declare_method("diff")

local value_name = declare_trait("value_name")
value_name:declare_method("value_name")

-- this method not only represents freezing from subsequent mutation, but also
-- returns an existing instance of the argument (if necessary, and structure
-- permitting) to enable efficient hash-consing
local freeze = declare_trait("freeze")
freeze:declare_method("freeze")

-- strict weak order, suitable for table.sort
local order = declare_trait("order")
order:declare_method("compare")

local glsl_print = declare_trait("glsl_print")
glsl_print:declare_method("glsl_print")

return {
	declare_trait = declare_trait,
	pretty_print = pretty_print,
	diff = diff,
	value_name = value_name,
	freeze = freeze,
	order = order,
	glsl_print = glsl_print,
}
