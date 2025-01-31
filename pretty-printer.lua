---@class PrettyPrint : { [integer] : string }
---@field opts PrettyPrintOpts
---@field depth integer
---@field table_tracker { [table] : boolean }
local PrettyPrint = {}
local PrettyPrint_mt = { __index = PrettyPrint }

local traits = require "traits"
local U = require "alicorn-utils"

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

---@alias PrettyPrintOpts {default_print: boolean?}

---@return PrettyPrint
---@param opts PrettyPrintOpts?
function PrettyPrint:new(opts)
	opts = opts or {}
	return setmetatable({ opts = { default_print = opts.default_print } }, PrettyPrint_mt)
end

---@param unknown any
---@param ... any
function PrettyPrint:any(unknown, ...)
	local ty = type(unknown)
	if ty == "string" then
		self[#self + 1] = string.format("%q", unknown)
	elseif ty == "function" then
		self:func(unknown)
	elseif ty == "table" then
		if self.depth and self.depth > 50 then
			self[#self + 1] = "DEPTH LIMIT EXCEEDED"
			return
		end
		local mt = getmetatable(unknown)
		local via_trait = mt and traits.pretty_print:get(mt)
		if via_trait then
			if self.opts.default_print then
				via_trait.default_print(unknown, self, ...)
			else
				via_trait.pretty_print(unknown, self, ...)
			end
		elseif mt and mt.__tostring then
			self[#self + 1] = tostring(unknown)
		elseif mt and mt.__call then
			self:func(mt.__call)
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

-- base16 colors: https://github.com/tinted-theming/home/blob/main/styling.md
local colors = {
	"\27[38;5;1m", -- base08
	-- "\27[38;5;16m", -- base09 (out of stock ANSI range)
	"\27[38;5;3m", -- base0A
	"\27[38;5;2m", -- base0B
	-- "\27[38;5;6m", -- base0C (uncomfortably close to base0D)
	"\27[38;5;4m", -- base0D
	"\27[38;5;5m", -- base0E
	-- "\27[38;5;17m", -- base0F (out of stock ANSI range)
}

function PrettyPrint:_color()
	return colors[1 + (((self.depth or 0) + #colors - 1) % #colors)]
end

function PrettyPrint:_resetcolor()
	return "\27[0m"
end

---@param array any[]
---@param ... any
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
---@param ... any
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
	---@type { [number] : boolean }
	local nums = {}
	---@type string[]
	local keyorder = {}
	---@type { [string]: any }
	local keymap = {}
	for k in pairs(fields) do
		if k == kind_field then
			self[#self + 1] = " "
			self[#self + 1] = fields.kind
		elseif hidden_fields[k] then
			-- nothing
		elseif type(k) == "number" then
			num = num + 1
			nums[k] = true
			local kstring = tostring(k)
			keyorder[#keyorder + 1] = kstring
			keymap[kstring] = k
		else
			count = count + 1
			local kstring = tostring(k)
			keyorder[#keyorder + 1] = kstring
			keymap[kstring] = k
		end
	end
	local seq = false
	if count == 0 and #nums == num then
		seq = true
	end
	if seq then
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
	else
		table.sort(keyorder)
		self[#self + 1] = self:_color()
		self[#self + 1] = " {\n"
		self[#self + 1] = self:_resetcolor()
		self:_indent()
		for i, kstring in ipairs(keyorder) do
			local k = keymap[kstring]
			if not hidden_fields[k] then
				local v = fields[k]
				self:_prefix()
				self[#self + 1] = self:_color()
				if type(k) == "string" then
					self[#self + 1] = k
				else
					self[#self + 1] = "["
					self[#self + 1] = self:_resetcolor()
					self[#self + 1] = tostring(k)
					self[#self + 1] = self:_color()
					self[#self + 1] = "]"
				end
				self[#self + 1] = " = "
				self[#self + 1] = self:_resetcolor()
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

---@param kind string
---@param fields table
---@param ... any
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
			self[#self + 1] = self:_color()
			self[#self + 1] = k
			self[#self + 1] = " = "
			self[#self + 1] = self:_resetcolor()
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
	if type(name) ~= "string" then
		error("IMPROPER PRETTYPRINT USAGE")
	end
	self[#self + 1] = name
end

---@param f async fun(...):...
function PrettyPrint:func(f)
	local d = debug.getinfo(f, "Su")
	---@type string[]
	local params = {}
	for i = 1, d.nparams do
		params[#params + 1] = debug.getlocal(f, i)
	end
	if d.isvararg then
		params[#params + 1] = "..."
	end
	self[#self + 1] =
		string.format("%s function(%s): %s:%d", d.what, table.concat(params, ", "), d.source, d.linedefined)
end

function PrettyPrint_mt:__tostring()
	return table.concat(self, "")
end

---@param unknown any
---@param ... any
---@return PrettyPrint
local function pretty_preprint(unknown, ...)
	local pp = PrettyPrint:new()
	pp:_enter() -- work around for printing in debug tags
	pp:_indent()
	pp:any(unknown, ...)
	pp:_dedent()
	pp:_exit()
	return pp
end

---@param unknown any
---@param ... any
---@return string
local function pretty_print(unknown, ...)
	local pp = PrettyPrint:new()
	pp:any(unknown, ...)
	return tostring(pp)
end

---@param unknown any
---@param ... any
---@return string
local function default_print(unknown, ...)
	local pp = PrettyPrint:new({ default_print = true })
	pp:any(unknown, ...)
	return tostring(pp)
end

---@param ... any
---@return string
local function s(...)
	local res = {}
	local args = table.pack(...)
	for i = 1, args.n do
		res[i] = pretty_print(args[i])
	end
	return table.concat(res, "    ")
end

---@param ... any
local function p(...)
	print(s(...))
end

_G["p"] = p

return {
	PrettyPrint = PrettyPrint,
	pretty_preprint = pretty_preprint,
	pretty_print = pretty_print,
	default_print = default_print,
	s = s,
	p = p,
}
