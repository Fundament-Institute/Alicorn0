local trait_type_method_mt = {
	__index = {
		declare_method = function(self, methodname) end,
	},
}

local trait_type_mt = {
	__index = {
		declare_method = function(self, methodname)
			if self.methods[methodname] then
				error("method already exists " .. methodname)
			end
			self.methods[methodname] = true
		end,
		implement_on = function(self, ty, methods)
			assert(type(ty) == "table")
			local implemented_methods = {}
			for k, v in pairs(self.methods) do
				implemented_methods[k] = methods[k]
					or error("missing method " .. k .. " implementing trait " .. self.name .. " on " .. str(ty))
			end
			self[ty] = implemented_methods
		end,
		get = function(self, ty)
			return self[ty] or error("not implemented on type " .. tostring(ty))
		end,
	},
}

local function declare_trait(name)
	return setmetatable({ name = name, methods = {} }, trait_type_mt)
end

return {
	declare_trait = declare_trait,
}
