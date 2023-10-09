local M = {}

function M.concat(...)
	local res = {}
	local inputs = { ... }
	for _, tab in ipairs(inputs) do
		for _, elem in ipairs(tab) do
			table.insert(res, elem)
		end
	end
	return res
end
