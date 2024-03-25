---@class PrettyPrint
local PrettyPrint = {}
local PrettyPrint_mt = { __index = PrettyPrint }

local prettyprintable = require "./pretty-printable-trait"

local kind_field = "kind"
local hidden_fields = {
	[kind_field] = true,
	capture = function(capture)
		if capture.bindings and capture.bindings.len then
			-- FIXME: we can't print all the bindings for a capture currently because we
			-- capture everything in scope and that's way too verbose
			-- if that gets fixed to only capture used bindings we can print more
			-- local ret = {}
			-- for i = 1, capture.bindings:len() do
			-- 	ret[i] = capture.bindings:get(i)
			-- end
			-- return ret
			return "runtime context with len=" .. tostring(capture.bindings:len())
		end
		return capture
	end,
}

function PrettyPrint.new()
	return setmetatable({}, PrettyPrint_mt)
end

function PrettyPrint:any(unknown, ...)
	local ty = type(unknown)
	if ty == "string" then
		self[#self + 1] = string.format("%q", unknown)
	elseif ty == "table" then
		if self.depth and self.depth > 50 then
			self[#self + 1] = "DEPTH LIMIT EXCEEDED"
			return
		end
		local mt = getmetatable(unknown)
		local via_trait = mt and prettyprintable[mt]
		if via_trait and via_trait.print then
			via_trait.print(unknown, self, ...)
		elseif mt and mt.__tostring then
			self[#self + 1] = tostring(unknown)
		else
			self:table(unknown)
		end
	else
		self[#self + 1] = tostring(unknown)
	end
end

function PrettyPrint:_prefix()
	if self.prefix then
		self[#self + 1] = self.prefix
	end
end

function PrettyPrint:_indent()
	if not self.prefix then
		self.prefix = " "
	else
		self.prefix = self.prefix .. " "
	end
end

function PrettyPrint:_enter()
	self.depth = (self.depth or 0) + 1
end

function PrettyPrint:_exit()
	self.depth = self.depth - 1
end

function PrettyPrint:_dedent()
	if self.prefix and #self.prefix > 1 then
		self.prefix = string.sub(self.prefix, 1, #self.prefix - 1)
	else
		self.prefix = nil
	end
end

local colors = {
	"\27[38;5;226m",
	"\27[38;5;255m",
	"\27[38;5;135m",
	"\27[38;2;40;40;40m",
}

function PrettyPrint:_color()
	return colors[1 + (((self.depth or 0) + #colors - 1) % #colors)]
end

function PrettyPrint:_resetcolor()
	return "\27[0m"
end

function PrettyPrint:array(array, ...)
	self:_enter()
	self[#self + 1] = self:_color()
	self[#self + 1] = "["
	self[#self + 1] = self:_resetcolor()
	for i, v in ipairs(array) do
		if i > 1 then
			self[#self + 1] = ", "
		end
		self:any(v, ...)
	end
	self[#self + 1] = self:_color()
	self[#self + 1] = "]"
	self[#self + 1] = self:_resetcolor()
	self:_exit()
end

---@param fields table
function PrettyPrint:table(fields, ...)
	-- i considered keeping track of a path of tables
	-- but it turned really horrible
	-- just grep its address until you find the original
	self[#self + 1] = "<"
	self[#self + 1] = tostring(fields)
	self[#self + 1] = ">"

	self.table_tracker = self.table_tracker or {}
	if self.table_tracker[fields] then
		return
	end
	self.table_tracker[fields] = true

	self:_enter()

	local count = 0
	local num = 0
	for k, v in pairs(fields) do
		if k == "kind" then
			self[#self + 1] = " "
			self[#self + 1] = fields.kind
		elseif hidden_fields[k] then
			-- nothing
		elseif type(k) == "number" then
			num = num + 1
		else
			count = count + 1
		end
	end
	if count == 0 then
		self[#self + 1] = self:_color()
		self[#self + 1] = "["
		self[#self + 1] = self:_resetcolor()
		for i, v in ipairs(fields) do
			if i > 1 then
				self[#self + 1] = ", "
			end
			self:any(v, ...)
		end
		self[#self + 1] = self:_color()
		self[#self + 1] = "]"
		self[#self + 1] = self:_resetcolor()
	elseif num == 0 and count == 1 then
		self[#self + 1] = self:_color()
		self[#self + 1] = "{"
		self[#self + 1] = self:_resetcolor()
		for k, v in pairs(fields) do
			if not hidden_fields[k] then
				self:any(v, ...)
			end
		end
		self[#self + 1] = self:_color()
		self[#self + 1] = "}"
		self[#self + 1] = self:_resetcolor()
	else
		self[#self + 1] = self:_color()
		self[#self + 1] = " {\n"
		self[#self + 1] = self:_resetcolor()
		self:_indent()
		for k, v in pairs(fields) do
			if not hidden_fields[k] then
				self:_prefix()
				self[#self + 1] = k
				self[#self + 1] = " = "
				self:any(v, ...)
				self[#self + 1] = ",\n"
			end
		end
		self:_dedent()
		self:_prefix()
		self[#self + 1] = self:_color()
		self[#self + 1] = "}"
		self[#self + 1] = self:_resetcolor()
	end

	self:_exit()
end

---@param fields table
function PrettyPrint:record(kind, fields, ...)
	local startLen = #self
	self:_enter()

	self[#self + 1] = self:_color()
	if kind then
		self[#self + 1] = kind
	end

	if #fields <= 1 then
		--self[#self + 1] = self:_color()
		local k, v = table.unpack(fields[1])
		if hidden_fields[k] then
			v = hidden_fields[k](v)
		end
		self[#self + 1] = "("
		self[#self + 1] = self:_resetcolor()
		self:any(v, ...)
		self[#self + 1] = self:_color()
		self[#self + 1] = ")"
	else
		--self[#self + 1] = self:_color()
		self[#self + 1] = " {\n"
		self[#self + 1] = self:_resetcolor()
		self:_indent()
		for _, pair in ipairs(fields) do
			local k, v = table.unpack(pair)
			if hidden_fields[k] then
				v = hidden_fields[k](v)
			end
			self:_prefix()
			self[#self + 1] = k
			self[#self + 1] = " = "
			self:any(v, ...)
			self[#self + 1] = ",\n"
		end
		self[#self + 1] = self:_color()
		-- if the record is big mark what's ending
		if (#self - startLen) > 50 then
			self:_prefix()
			self[#self + 1] = "--end "
			self[#self + 1] = kind
			self[#self + 1] = "\n"
		end
		self:_dedent()
		self:_prefix()
		self[#self + 1] = "}"
	end

	self[#self + 1] = self:_resetcolor()
	self:_exit()
end

---@param name string
function PrettyPrint:unit(name)
	self[#self + 1] = name
end

function PrettyPrint_mt:__tostring()
	return table.concat(self, "")
end

_G["p"] = function(...)
	local res = {}
	for i, v in ipairs { ... } do
		local pp = PrettyPrint:new()
		pp:any(v)
		res[i] = tostring(pp)
	end
	print(table.concat(res))
end

return {
	PrettyPrint = PrettyPrint,
	prettyprintable = prettyprintable,
}
