-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

local backend_mt = {
	__index = {
		compile = function(self, code)
			if self.cache[code] then
				return self.cache[code]
			end
			local inputs = {}
			for i, v in ipairs(code.inputs) do
				inputs[i] = self:compile(v)
			end
			local selection = self.dispatch[code.operator]
			local ok, res, docache = pcall(selection.handler, code.type_parameters, code.bound_data, inputs)
			if not ok then
				error("The compilation handler from " .. selection.origin.name .. " had an unhandled error " .. res)
			end
			if docache then
				self.cache[code] = res
			end
			return res
		end,
	},
}

local function backend(components)
	local dispatch = {}
	for i, comp in ipairs(components) do
		for token, handler in pairs(comp.handlers) do
			if dispatch[token] then
				error "duplicate definition of operator in backend"
			else
				dispatch[token] = { handler = handler, origin = comp }
			end
		end
	end

	local self = {
		dispatch = dispatch,
	}

	return setmetatable(self, backend_mt)
end

return backend
