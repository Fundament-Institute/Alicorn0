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

function M.notail(...)
	return ...
end
function M.tag(name, info, fn, ...)
	return M.notail(fn(...))
end

return M
