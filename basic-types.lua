-- a type is defined by the type constructor and the arguments passed to that constructor.

local function new_memo()
	return { follows = {}, val = nil, hasval = false }
end

local function get_memo_cell(memo, args)
	for _, v in ipairs(args) do
		if memo.follows[v] then
			memo = memo.follows[v]
		else
			memo.follows[v] = new_memo()
			memo = memo.follows[v]
		end
	end
	return memo
end

local function set_memo(memo, val)
	memo.hasval = true
	memo.val = val
end

local function instantiate_kind(self, ...)
	local args = { ... }
	local memo = self.memo
	for i, v in ipairs(self.params) do
		memo = v:memoizer(memo, args[i])
	end
	if memo.hasval then
		return memo.val
	else
		set_memo(memo, self.build({ kind = self, args = args }, ...))
		return memo.val
	end
end

local kind_mt = {
	__call = instantiate_kind,
}

local function makekind(name, params, build)
	local self = {
		name,
		params = params,
		build = build,
		memo = new_memo(),
	}
	return setmetatable(self, kind_mt)
end

local num_kind = makekind("number", {}, function(self)
	self.storage = { kind = "special", "number" }
	function self:memoizer(memo, val)
		return get_memo_cell(memo, { val })
	end
	return self
end)

local type_kind = makekind("type", {}, function(self)
	self.storage = { kind = "special", "type" }
	function self:memoizer(memo, val)
		return get_memo_cell(memo, { val })
	end
	return self
end)

local types = {}

types.num = instantiate_kind(num_kind)
types.type = instantiate_kind(type_kind)

types.array = makekind("array", { types.type }, function(self, elem)
	self.storage = { kind = "special", "array", elem }
	function self:memoizer(memo, val)
		memo = get_memo_cell(memo, { #val })
		return get_memo_cell(memo, val)
	end
	return self
end)

types.tuple = makekind("tuple", { types.array(types.type) }, function(self, components)
	self.storage = { kind = "special", "tuple", components }
	function self:memoizer(memo, val)
		for i, v in ipairs(components) do
			memo = v:memoizer(memo, val[i])
		end
		return memo
	end
	return self
end)

types.enum = makekind("enum", { types.array(types.type) }, function(self, variants)
	self.storage = { kind = "special", "enum", variants }
	function self:memoizer(memo, val)
		memo = get_memo_cell(memo, { val.kind })
		return variants[val.kind]:memoizer(memo, val[1])
	end
	return self
end)

types.fn = makekind("fn", { types.type, types.type }, function(self, args, rets)
	self.storage = { kind = "special", "closure", args, rets }
	function self:memoizer(memo, val)
		return get_memo_cell(memo, { val }) -- don't know how to memoize by function behavior yet
	end
	return self
end)

types.makekind = makekind

return types
