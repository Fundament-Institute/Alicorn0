-- provide ways to construct all terms
-- checker untyped term and typechecking context -> typed term
-- evaluator takes typed term and runtime context -> value

-- type checker monad
-- error handling and metavariable unification facilities
--
-- typechecker is allowed to fail, typechecker monad carries failures upwards
--   for now fail fast, but design should vaguely support multiple failures

-- metavariable unification
--   a metavariable is like a variable butmore meta
--   create a set of variables -> feed into code -> evaluate with respect to them
--   in order for the values produced by these two invocations to be the same, what would the metavariales need to be bound to?
--   (this is like symbolic execution)
--
-- in the typechecking monad we create a metavariable which takes a type and produces a term or value of that type and
-- we can unfy two values against each other to solve their metavariables or it can fail
-- for now unification with equality is the only kind of constraint. eventuall may be others but that's hard/no need right now

-- we will use lua errors for handling here - use if, error not assert so JIT understands
-- metavariables = table, edit the table, this is the stateful bit the monad has
-- methods on metavariable that bind equal to some value, if it is already bound it has to unify which can fail, failure cascades
-- thing passed to bind equl method on metavariable is a 'value' - enumerated datatype, like term but less cases
--   scaffolding - need to add cases here foreach new value variant
--
-- create metavariable, pass in as arg to lambda, get back result, unify against another type
--   it's ok if a metavariable never gets constrained during part of typechecking
-- give metavariables sequential ids (tracked in typechecker_state)

-- metavariable state transitions, can skip steps but must always move down

-- unbound
-- vvv
-- bound to exactly another metavariable - have a reference to a metavariable
-- vvv
-- bound to a value - have a reference to a value

-- when binding to another metavariable bind the one with a greater index to the lesser index

local metalang = require "./metalanguage"
--local types = require "./typesystem"

local fibbuf = require "./fibonacci-buffer"

local gen = require "./terms-generators"
local derivers = require "./derivers"
local map = gen.declare_map
local array = gen.declare_array

local function getmvinfo(id, mvs)
	if mvs == nil then
		return
	end
	-- if this is slow fixme later
	return mvs[id] or getmvinfo(id, mvs.prev_mvs)
end

local metavariable_mt

metavariable_mt = {
	__index = {
		get_value = function(self)
			local canonical = self:get_canonical()
			local canonical_info = getmvinfo(canonical.id, self.typechecker_state.mvs)
			return canonical_info.bound_value or values.free(free.metavariable(canonical))
		end,
		get_canonical = function(self)
			local canonical_id = self.typechecker_state:get_canonical_id(self.id)

			if canonical_id ~= self.id then
				return setmetatable({
					id = canonical_id,
					typechecker_state = self.typechecker_state,
				}, metavariable_mt):get_canonical()
			end

			return self
		end,
		-- this gets called to bind to any value that isn't another metavariable
		bind_value = function(self, value)
			-- FIXME: if value is a metavariable (free w/ metavariable) call bind_metavariable here?
			local canonical = self:get_canonical()
			local canonical_info = getmvinfo(canonical.id, self.typechecker_state.mvs)
			if canonical_info.bound_value and canonical_info.bound_value ~= value then
				-- unify the two values, throws lua error if can't
				value = canonical_info.bound_value:unify(value)
			end
			self.typechecker_state.mvs[canonical.id] = {
				bound_value = value,
			}
			return value
		end,
		bind_metavariable = function(self, other)
			if self == other then
				return
			end

			if getmetatable(other) ~= metavariable_mt then
				p(self, other, getmetatable(self), getmetatable(other))
				error("metavariable.bind should only be called with metavariable as arg")
			end

			if self.typechecker_state ~= other.typechecker_state then
				error("trying to mix metavariables from different typechecker_states")
			end

			if self.id == other.id then
				return
			end

			if self.id < other.id then
				return other:bind_metavariable(self)
			end

			local this = getmvinfo(self.id, self.typechecker_state.mvs)
			if this.bound_value then
				error("metavariable is already bound to a value")
			end

			self.typechecker_state.mvs[self.id] = {
				bound_mv_id = other.id,
			}
		end,
	},
}
local metavariable_type = gen.declare_foreign(gen.metatable_equality(metavariable_mt))

local typechecker_state_mt
typechecker_state_mt = {
	__index = {
		metavariable = function(self) -- -> metavariable instance
			self.next_metavariable_id = self.next_metavariable_id + 1
			self.mvs[self.next_metavariable_id] = {}
			return setmetatable({
				id = self.next_metavariable_id,
				typechecker_state = self,
			}, metavariable_mt)
		end,
		get_canonical_id = function(self, mv_id) -- -> number
			local mvinfo = getmvinfo(mv_id, self.mvs)
			if mvinfo.bound_mv_id then
				local final_id = self:get_canonical_id(mvinfo.bound_mv_id)
				if final_id ~= mvinfo.bound_mv_id then
					-- ok to mutate rather than setting in self.mvs here as collapsing chain is idempotent
					mvinfo.bound_mv_id = final_id
				end
				return final_id
			end
			return mv_id
		end,
	},
}

local function typechecker_state()
	return setmetatable({
		next_metavariable_id = 0,
		mvs = { prev_mvs = nil },
	}, typechecker_state_mt)
end

-- freeze and then commit or revert
-- like a transaction
local function speculate(f, ...)
	mvs = {
		prev_mvs = mvs,
	}
	local commit, result = f(...)
	if commit then
		-- commit
		for k, v in pairs(mvs) do
			if k ~= "prev_mvs" then
				prev_mvs[k] = mvs[k]
			end
		end
		mvs = mvs.prev_mvs
		return result
	else
		-- revert
		mvs = mvs.prev_mvs
		-- intentionally don't return result if set if not committing to prevent smuggling out of execution
		return nil
	end
end

---@module "./types/checkable"
local checkable_term = gen.declare_type()
---@module "./types/inferrable"
local inferrable_term = gen.declare_type()
---@module "./types/typed"
local typed_term = gen.declare_type()
---@module "./types/free"
local free = gen.declare_type()
---@module "./types/placeholder"
local placeholder_debug = gen.declare_type()
---@module "./types/value"
local value = gen.declare_type()
---@module "./types/neutral"
local neutral_value = gen.declare_type()
---@module "./types/binding"
local binding = gen.declare_type()
---@module "./types/expression_goal"
local expression_goal = gen.declare_type()

local runtime_context_mt

---@class RuntimeContext
---@field bindings unknown
local RuntimeContext = {}
function RuntimeContext:get(index)
	return self.bindings:get(index)
end
function RuntimeContext:append(value)
	-- TODO: typecheck
	local copy = { bindings = self.bindings:append(value) }
	return setmetatable(copy, runtime_context_mt)
end
function RuntimeContext:eq(other)
	local omt = getmetatable(other)
	if omt ~= runtime_context_mt then
		return false
	end
	local sb, ob = self.bindings, other.bindings
	local n, on = sb:len(), ob:len()
	if n ~= on then
		return false
	end
	for i = 1, n do
		if sb:get(i) ~= ob:get(i) then
			return false
		end
	end
	return true
end

runtime_context_mt = {
	__index = RuntimeContext,
	__eq = RuntimeContext.eq,
}

local function runtime_context()
	local self = {}
	self.bindings = fibbuf()
	return setmetatable(self, runtime_context_mt)
end

local typechecking_context_mt

---@class TypecheckingContext
---@field runtime_context RuntimeContext
---@field bindings unknown
local TypecheckingContext = {}
---get the name of a binding in a TypecheckingContext
---@param index integer
---@return string
function TypecheckingContext:get_name(index)
	return self.bindings:get(index).name
end
function TypecheckingContext:dump_names()
	for i = 1, #self do
		print(i, self:get_name(i))
	end
end
function TypecheckingContext:format_names()
	local msg = ""
	for i = 1, #self do
		msg = msg .. tostring(i) .. "\t" .. self:get_name(i) .. "\n"
	end
	return msg
end
function TypecheckingContext:get_type(index)
	return self.bindings:get(index).type
end
function TypecheckingContext:get_runtime_context()
	return self.runtime_context
end
function TypecheckingContext:append(name, type, val, anchor) -- value is optional, anchor is optional
	-- TODO: typecheck
	if name == nil or type == nil then
		error("bug!!!")
	end
	if value.value_check(type) ~= true then
		print("type", type)
		p(type)
		for k, v in pairs(type) do
			print(k, v)
		end
		print(getmetatable(type))
		error "TypecheckingContext:append type parameter of wrong type"
	end
	if type:is_closure() then
		error "BUG!!!"
	end
	local copy = {
		bindings = self.bindings:append({ name = name, type = type }),
		runtime_context = self.runtime_context:append(
			val or value.neutral(neutral_value.free(free.placeholder(#self + 1, placeholder_debug(name, anchor))))
		),
	}
	return setmetatable(copy, typechecking_context_mt)
end

typechecking_context_mt = {
	__index = TypecheckingContext,
	__len = function(self)
		return self.bindings:len()
	end,
}

local function typechecking_context()
	local self = {}
	self.bindings = fibbuf()
	self.runtime_context = runtime_context()
	return setmetatable(self, typechecking_context_mt)
end

-- empty for now, just used to mark the table
local module_mt = {}

local runtime_context_type = gen.declare_foreign(gen.metatable_equality(runtime_context_mt))
local typechecking_context_type = gen.declare_foreign(gen.metatable_equality(typechecking_context_mt))
local prim_user_defined_id = gen.declare_foreign(function(val)
	return type(val) == "table" and type(val.name) == "string"
end)

expression_goal:define_enum("expression_goal", {
	-- infer
	{ "infer" },
	-- check to a goal type
	{ "check", {
		"goal_type",
		value,
	} },
	{
		"mechanism",
		{
			-- TODO
			"TODO",
			value,
		},
	},
})

-- terms that don't have a body yet
binding:define_enum("binding", {
	{ "let", {
		"name",
		gen.builtin_string,
		"expr",
		inferrable_term,
	} },
	{ "tuple_elim", {
		"names",
		array(gen.builtin_string),
		"subject",
		inferrable_term,
	} },
	{
		"annotated_lambda",
		{
			"param_name",
			gen.builtin_string,
			"param_annotation",
			inferrable_term,
			"anchor",
			gen.anchor_type,
		},
	},
})

local function let_helper(pp, name, expr, context)
	pp:unit(name)

	pp:unit(pp:_color())
	pp:unit(" = ")
	pp:unit(pp:_resetcolor())

	pp:_indent()
	pp:any(expr, context)
	pp:_dedent()

	context = context:append(name)

	return context
end
local function tuple_elim_helper(pp, names, subject, context)
	local inner_context = context

	pp:unit(pp:_color())
	pp:unit("(")
	pp:unit(pp:_resetcolor())

	for i, name in names:ipairs() do
		inner_context = inner_context:append(name)

		if i > 1 then
			pp:unit(pp:_color())
			pp:unit(", ")
			pp:unit(pp:_resetcolor())
		end

		pp:unit(name)
	end

	pp:unit(pp:_color())
	pp:unit(") = ")
	pp:unit(pp:_resetcolor())

	pp:any(subject, context)

	return inner_context
end
local function tuple_type_helper(pp, members, names)
	local m = #members

	if m == 0 then
		return
	end

	if not names then
		-- get them from last (outermost) decl
		-- the name of the last member is lost in this case
		names = members[m][1]
	end

	local n = type(names) == "table" and #names or 0

	for i, mem in ipairs(members) do
		if i > 1 then
			pp:unit(" ")
		end

		pp:unit(pp:_color())
		pp:unit("(")
		pp:unit(pp:_resetcolor())

		if i > n then
			pp:unit(string.format("#unk%d", i))
		else
			pp:unit(names[i])
		end

		pp:unit(pp:_color())
		pp:unit(" : ")
		pp:unit(pp:_resetcolor())

		pp:any(mem[2], mem[3])

		pp:unit(pp:_color())
		pp:unit(")")
		pp:unit(pp:_resetcolor())
	end
end
local function as_any_tuple_type(term)
	local ok, decls = term:as_tuple_type()
	if ok then
		return ok, decls
	end

	local ok, decls = term:as_prim_tuple_type()
	if ok then
		return ok, decls
	end

	return false
end
local prettyprinting_context_mt = {}
local PrettyprintingContext = {}
function PrettyprintingContext.new()
	local self = {}
	self.bindings = fibbuf()
	return setmetatable(self, prettyprinting_context_mt)
end
function PrettyprintingContext.from_typechecking_context(context)
	local self = {}
	self.bindings = context.bindings
	return setmetatable(self, prettyprinting_context_mt)
end
function PrettyprintingContext.from_runtime_context(context)
	local self = {}
	local bindings = fibbuf()
	for i = 1, context.bindings:len() do
		bindings = bindings:append({ name = string.format("#rctx%d", i) })
	end
	self.bindings = bindings
	return setmetatable(self, prettyprinting_context_mt)
end
function PrettyprintingContext:get_name(index)
	return self.bindings:get(index).name
end
function PrettyprintingContext:append(name)
	if type(name) ~= "string" then
		error("PrettyprintingContext:append must append string name")
	end
	local copy = {}
	copy.bindings = self.bindings:append({ name = name })
	return setmetatable(copy, prettyprinting_context_mt)
end
prettyprinting_context_mt.__index = PrettyprintingContext
function prettyprinting_context_mt:__len()
	return self.bindings:len()
end
local prettyprinting_context_type = gen.declare_foreign(gen.metatable_equality(prettyprinting_context_mt))
local function ensure_context(context)
	if prettyprinting_context_type.value_check(context) == true then
		return context
	elseif typechecking_context_type.value_check(context) == true then
		return PrettyprintingContext.from_typechecking_context(context)
	elseif runtime_context_type.value_check(context) == true then
		return PrettyprintingContext.from_runtime_context(context)
	else
		print("!!!!!!!!!! MISSING CONTEXT !!!!!!!!!!!!!!")
		print("making something up")
		return PrettyprintingContext.new()
	end
end
local binding_override_pretty = {
	let = function(self, pp, context)
		local name, expr = self:unwrap_let()
		context = ensure_context(context)

		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("binding.let ")
		pp:unit(pp:_resetcolor())
		let_helper(pp, name, expr, context)

		pp:_exit()
	end,
	tuple_elim = function(self, pp, context)
		local names, subject = self:unwrap_tuple_elim()
		context = ensure_context(context)

		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("binding.let ")
		pp:unit(pp:_resetcolor())
		tuple_elim_helper(pp, names, subject, context)

		pp:_exit()
	end,
	annotated_lambda = function(self, pp, context)
		local param_name, param_annotation, anchor = self:unwrap_annotated_lambda()
		context = ensure_context(context)

		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("binding.\u{03BB} ")
		pp:unit(pp:_resetcolor())

		pp:unit(param_name)

		pp:unit(pp:_color())
		pp:unit(" : ")
		pp:unit(pp:_resetcolor())

		pp:any(param_annotation, context)

		pp:_exit()
	end,
}

-- checkable terms need a goal type to typecheck against
checkable_term:define_enum("checkable", {
	{ "inferrable", { "inferrable_term", inferrable_term } },
	{ "tuple_cons", { "elements", array(checkable_term) } },
	{ "prim_tuple_cons", { "elements", array(checkable_term) } },
	{ "lambda", {
		"param_name",
		gen.builtin_string,
		"body",
		checkable_term,
	} },
	-- TODO: enum_cons
})
-- inferrable terms can have their type inferred / don't need a goal type
inferrable_term:define_enum("inferrable", {
	{ "bound_variable", { "index", gen.builtin_number } },
	{ "typed", {
		"type",
		value,
		"usage_counts",
		array(gen.builtin_number),
		"typed_term",
		typed_term,
	} },
	{
		"annotated_lambda",
		{
			"param_name",
			gen.builtin_string,
			"param_annotation",
			inferrable_term,
			"body",
			inferrable_term,
			"anchor",
			gen.anchor_type,
		},
	},
	{
		"pi",
		{
			"param_type",
			inferrable_term,
			"param_info",
			checkable_term,
			"result_type",
			inferrable_term,
			"result_info",
			checkable_term,
		},
	},
	{ "application", {
		"f",
		inferrable_term,
		"arg",
		checkable_term,
	} },
	{ "tuple_cons", { "elements", array(inferrable_term) } },
	{
		"tuple_elim",
		{
			"names",
			array(gen.builtin_string),
			"subject",
			inferrable_term,
			"body",
			inferrable_term,
		},
	},
	{ "tuple_type", { "definition", inferrable_term } },
	{ "record_cons", { "fields", map(gen.builtin_string, inferrable_term) } },
	{
		"record_elim",
		{
			"subject",
			inferrable_term,
			"field_names",
			array(gen.builtin_string),
			"body",
			inferrable_term,
		},
	},
	{ "enum_cons", {
		"enum_type",
		value,
		"constructor",
		gen.builtin_string,
		"arg",
		inferrable_term,
	} },
	{ "enum_elim", {
		"subject",
		inferrable_term,
		"mechanism",
		inferrable_term,
	} },
	{ "enum_type", { "definition", inferrable_term } },
	{ "object_cons", { "methods", map(gen.builtin_string, inferrable_term) } },
	{ "object_elim", {
		"subject",
		inferrable_term,
		"mechanism",
		inferrable_term,
	} },
	{ "let", {
		"name",
		gen.builtin_string,
		"expr",
		inferrable_term,
		"body",
		inferrable_term,
	} },
	{ "operative_cons", {
		"operative_type",
		inferrable_term,
		"userdata",
		inferrable_term,
	} },
	{ "operative_type_cons", {
		"handler",
		checkable_term,
		"userdata_type",
		inferrable_term,
	} },
	{ "level_type" },
	{ "level0" },
	{ "level_suc", { "previous_level", inferrable_term } },
	{ "level_max", {
		"level_a",
		inferrable_term,
		"level_b",
		inferrable_term,
	} },
	--{"star"},
	--{"prop"},
	--{"prim"},
	{ "annotated", {
		"annotated_term",
		checkable_term,
		"annotated_type",
		inferrable_term,
	} },
	{ "prim_tuple_cons", { "elements", array(inferrable_term) } }, -- prim
	{
		"prim_user_defined_type_cons",
		{
			"id",
			prim_user_defined_id, -- prim_user_defined_type
			"family_args",
			array(inferrable_term), -- prim
		},
	},
	{ "prim_tuple_type", { "decls", inferrable_term } }, -- just like an ordinary tuple type but can only hold prims
	{
		"prim_function_type",
		{
			"param_type",
			inferrable_term, -- must be a prim_tuple_type
			-- primitive functions can only have explicit arguments
			"result_type",
			inferrable_term, -- must be a prim_tuple_type
			-- primitive functions can only be pure for now
		},
	},
	{ "prim_wrapped_type", { "type", inferrable_term } },
	{ "prim_unstrict_wrapped_type", { "type", inferrable_term } },
	{ "prim_wrap", { "content", inferrable_term } },
	{ "prim_unstrict_wrap", { "content", inferrable_term } },
	{ "prim_unwrap", { "container", inferrable_term } },
	{ "prim_unstrict_unwrap", { "container", inferrable_term } },
	{
		"prim_if",
		{
			"subject",
			checkable_term, -- checkable because we always know must be of prim_bool_type
			"consequent",
			inferrable_term,
			"alternate",
			inferrable_term,
		},
	},
	{
		"prim_intrinsic",
		{
			"source",
			checkable_term,
			"type",
			inferrable_term, --checkable_term,
			"anchor",
			gen.anchor_type,
		},
	},
})

-- the only difference compared to typed_let_or_tuple_elim is lack of length
local function inferrable_let_or_tuple_elim(pp, term, context)
	pp:_enter()

	local name, expr, names, subject
	while true do
		if term:is_let() then
			name, expr, term = term:unwrap_let()

			-- rear-loading prefix to cheaply handle first loop not needing prefix
			pp:unit(pp:_color())
			pp:unit("inferrable.let ")
			pp:unit(pp:_resetcolor())
			context = let_helper(pp, name, expr, context)
			pp:unit("\n")
			pp:_prefix()
		elseif term:is_tuple_elim() then
			names, subject, term = term:unwrap_tuple_elim()

			pp:unit(pp:_color())
			pp:unit("inferrable.let ")
			pp:unit(pp:_resetcolor())
			context = tuple_elim_helper(pp, names, subject, context)
			pp:unit("\n")
			pp:_prefix()
		else
			break
		end
	end

	pp:any(term, context)

	pp:_exit()
end
-- the only difference compared to typed_destructure_helper is lack of length
local function inferrable_destructure_helper(term, context)
	if term:is_let() then
		-- destructuring with a let effectively just renames the parameter
		-- thus it's usually superfluous to write code like this
		-- and probably unwise to elide the let
		-- but some operatives that are generic over lets and tuple-elims do this
		-- e.g. forall, lambda
		-- so we pretty this anyway
		local name, expr, body = term:unwrap_let()
		local ok, index = expr:as_bound_variable()
		local is_destructure = ok and index == #context
		if is_destructure then
			context = context:append(name)
			return true, true, name, body, context
		end
	elseif term:is_tuple_elim() then
		local names, subject, body = term:unwrap_tuple_elim()
		local ok, index = subject:as_bound_variable()
		local is_destructure = ok and index == #context
		if is_destructure then
			for i, name in names:ipairs() do
				context = context:append(name)
			end
			return true, false, names, body, context
		end
	end
	return false, false, nil, term, context
end
-- mostly the same as typed_tuple_type_flatten
-- differences:
-- - enum_type existing and checking
-- - lambda is different
local function inferrable_tuple_type_flatten(definition, context)
	local enum_type, constructor, arg = definition:unwrap_enum_cons()
	local ok, universe = enum_type:as_tuple_defn_type()
	-- TODO: what is universe?
	if not ok then
		error("override_pretty: inferrable.tuple_type: enum_type must be tuple_defn_type")
	end
	if constructor == "empty" then
		return {}, 0
	elseif constructor == "cons" then
		local elements = arg:unwrap_tuple_cons()
		local definition = elements[1]
		local f = elements[2]
		local ok, param_name, param_annotation, body, anchor = f:as_annotated_lambda()
		if not ok then
			error("override_pretty: inferrable.tuple_type: tuple decl must be a lambda")
		end
		local inner_context = context:append(param_name)
		local is_destructure, is_rename, names, body, inner_context = inferrable_destructure_helper(body, inner_context)
		local prev, n = inferrable_tuple_type_flatten(definition, context)
		n = n + 1
		prev[n] = { names, body, inner_context }
		return prev, n
	else
		error("override_pretty: inferrable.tuple_type: unknown tuple type data constructor")
	end
end
local checkable_term_override_pretty = {
	inferrable = function(self, pp, context)
		local inferrable_term = self:unwrap_inferrable()
		context = ensure_context(context)
		pp:any(inferrable_term, context)
	end,
}
local inferrable_term_override_pretty = {
	-- copypaste of typed.bound_variable
	bound_variable = function(self, pp, context)
		local index = self:unwrap_bound_variable()
		context = ensure_context(context)

		pp:_enter()

		if #context >= index then
			pp:unit(context:get_name(index))
		else
			-- TODO: warn on context too short?
			pp:unit(pp:_color())
			pp:unit("inferrable.bound_variable(")
			pp:unit(pp:_resetcolor())

			pp:unit(tostring(index))

			pp:unit(pp:_color())
			pp:unit(")")
			pp:unit(pp:_resetcolor())
		end

		pp:_exit()
	end,
	typed = function(self, pp, context)
		local type, usage_counts, typed_term = self:unwrap_typed()
		context = ensure_context(context)

		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("inferrable.the (")
		pp:unit(pp:_resetcolor())

		pp:any(type)

		pp:unit(pp:_color())
		pp:unit(") (")
		pp:unit(pp:_resetcolor())

		pp:any(typed_term, context)

		pp:unit(pp:_color())
		pp:unit(")")
		pp:unit(pp:_resetcolor())

		pp:_exit()
	end,
	-- some similarities to inferrable.pi and typed.lambda
	annotated_lambda = function(self, pp, context)
		local param_name, param_annotation, body, anchor = self:unwrap_annotated_lambda()
		context = ensure_context(context)
		local inner_context = context:append(param_name)
		local is_tuple_type, decls = as_any_tuple_type(param_annotation)
		local is_destructure, is_rename, names, body, inner_context = inferrable_destructure_helper(body, inner_context)
		if is_rename then
			param_name = names
			is_destructure = false
		end

		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("inferrable.\u{03BB} ")
		pp:unit(pp:_resetcolor())

		if is_tuple_type and is_destructure then
			local members = inferrable_tuple_type_flatten(decls, context)

			if #members == 0 then
				pp:unit(pp:_color())
				pp:unit("()")
				pp:unit(pp:_resetcolor())
			else
				tuple_type_helper(pp, members, names)
			end
		elseif is_destructure then
			-- tuple_elim on param but its type isn't a tuple type???
			-- probably shouldn't happen, but here's a handler
			pp:unit(pp:_color())
			pp:unit("(")
			pp:unit(pp:_resetcolor())

			for i, name in names:ipairs() do
				if i > 1 then
					pp:unit(" ")
				end
				pp:unit(name)
			end

			pp:unit(pp:_color())
			pp:unit(") : ")
			pp:unit(pp:_resetcolor())

			pp:any(param_annotation, context)
		else
			pp:unit(param_name)

			pp:unit(pp:_color())
			pp:unit(" : ")
			pp:unit(pp:_resetcolor())

			pp:any(param_annotation, context)
		end

		pp:unit(pp:_color())
		pp:unit(" ->")
		pp:unit(pp:_resetcolor())

		if body:is_let() or body:is_tuple_elim() then
			pp:unit("\n")
			pp:_indent()
			pp:_prefix()
			pp:any(body, inner_context)
			pp:_dedent()
		else
			pp:unit(" ")
			pp:any(body, inner_context)
		end

		pp:_exit()
	end,
	-- some similarities to inferrable.annotated_lambda and inferrable.prim_function_type
	-- copypaste of typed.pi
	pi = function(self, pp, context)
		-- extracting parameter names from the destructure of the result
		-- so that we get the name of the last parameter
		-- name of the last result is still lost
		local param_type, param_info, result_type, result_info = self:unwrap_pi()
		context = ensure_context(context)
		local result_context = context
		local param_is_tuple_type, param_decls = as_any_tuple_type(param_type)
		local ok, param_name, param_annotation, result_body, result_anchor = result_type:as_annotated_lambda()
		if not ok then
			error("override_pretty: inferrable.pi: result_type must be a lambda")
		end
		result_context = result_context:append(param_name)
		local result_is_destructure, result_is_rename, param_names, result_body, result_context =
			inferrable_destructure_helper(result_body, result_context)
		if result_is_rename then
			param_name = param_names
			result_is_destructure = false
		end
		local result_is_tuple_type, result_decls = as_any_tuple_type(result_body)

		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("inferrable.\u{03A0} ")
		pp:unit(pp:_resetcolor())

		if param_is_tuple_type and result_is_destructure then
			local members = inferrable_tuple_type_flatten(param_decls, context)

			if #members == 0 then
				pp:unit(pp:_color())
				pp:unit("()")
				pp:unit(pp:_resetcolor())
			else
				tuple_type_helper(pp, members, param_names)
			end
		elseif result_is_destructure then
			-- tuple_elim on params but params aren't a tuple type???
			-- probably shouldn't happen, but here's a handler
			pp:unit(pp:_color())
			pp:unit("(")
			pp:unit(pp:_resetcolor())

			for i, name in param_names:ipairs() do
				if i > 1 then
					pp:unit(" ")
				end
				pp:unit(name)
			end

			pp:unit(pp:_color())
			pp:unit(") : ")
			pp:unit(pp:_resetcolor())

			pp:any(param_type, context)
		else
			pp:unit(param_name)

			pp:unit(pp:_color())
			pp:unit(" : ")
			pp:unit(pp:_resetcolor())

			pp:any(param_type, context)
		end

		pp:unit(pp:_color())
		pp:unit(" -> ")
		pp:unit(pp:_resetcolor())

		if result_is_tuple_type then
			local members = inferrable_tuple_type_flatten(result_decls, result_context)

			if #members == 0 then
				pp:unit(pp:_color())
				pp:unit("()")
				pp:unit(pp:_resetcolor())
			else
				tuple_type_helper(pp, members)
			end
		else
			pp:any(result_body, result_context)
		end

		pp:_exit()
	end,
	application = function(self, pp, context)
		local f, arg = self:unwrap_application()
		context = ensure_context(context)

		-- handle nested applications
		local function application_inner(f, arg)
			local f_is_application, f_f, f_arg = f:as_application()
			local f_is_typed, f_type, f_usage_counts, f_typed_term = f:as_typed()
			local f_is_bound_variable, f_index = false
			if f_is_typed then
				f_is_bound_variable, f_index = f_typed_term:as_bound_variable()
			end

			pp:_enter()

			-- print pretty on certain conditions, or fall back to apply()
			if
				(f_is_application or (f_is_typed and f_is_bound_variable and #context >= f_index))
				and (arg:is_tuple_cons() or arg:is_prim_tuple_cons())
			then
				if f_is_application then
					application_inner(f_f, f_arg)
				else
					pp:unit(context:get_name(f_index))
				end

				local ok, elements = arg:as_tuple_cons()
				elements = ok and elements or arg:unwrap_prim_tuple_cons()

				pp:unit(pp:_color())
				pp:unit("(")
				pp:unit(pp:_resetcolor())

				for i, arg in ipairs(elements) do
					if i > 1 then
						pp:unit(pp:_color())
						pp:unit(", ")
						pp:unit(pp:_resetcolor())
					end

					pp:any(arg, context)
				end

				pp:unit(pp:_color())
				pp:unit(")")
				pp:unit(pp:_resetcolor())
			else
				-- if we're here then the args are probably horrible
				-- add some newlines
				pp:unit(pp:_color())
				pp:unit("inferrable.apply(")
				pp:unit(pp:_resetcolor())
				pp:unit("\n")

				pp:_indent()

				pp:_prefix()
				pp:any(f, context)
				pp:unit(pp:_color())
				pp:unit(",")
				pp:unit(pp:_resetcolor())
				pp:unit("\n")

				pp:_prefix()
				pp:any(arg, context)
				pp:unit("\n")

				pp:_dedent()

				pp:_prefix()
				pp:unit(pp:_color())
				pp:unit(")")
				pp:unit(pp:_resetcolor())
			end

			pp:_exit()
		end

		application_inner(f, arg)
	end,
	tuple_elim = function(self, pp, context)
		context = ensure_context(context)
		inferrable_let_or_tuple_elim(pp, self, context)
	end,
	tuple_type = function(self, pp, context)
		local definition = self:unwrap_tuple_type()
		context = ensure_context(context)
		local members = inferrable_tuple_type_flatten(definition, context)

		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("inferrable.tuple_type[")
		pp:unit(pp:_resetcolor())

		tuple_type_helper(pp, members)

		pp:unit(pp:_color())
		pp:unit("]")
		pp:unit(pp:_resetcolor())

		pp:_exit()
	end,
	let = function(self, pp, context)
		context = ensure_context(context)
		inferrable_let_or_tuple_elim(pp, self, context)
	end,
	prim_tuple_type = function(self, pp, context)
		local decls = self:unwrap_prim_tuple_type()
		context = ensure_context(context)
		local members = inferrable_tuple_type_flatten(decls, context)

		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("inferrable.prim_tuple_type[")
		pp:unit(pp:_resetcolor())

		tuple_type_helper(pp, members)

		pp:unit(pp:_color())
		pp:unit("]")
		pp:unit(pp:_resetcolor())

		pp:_exit()
	end,
	-- some similarities to inferrable.pi
	-- copypaste of typed.prim_function_type
	prim_function_type = function(self, pp, context)
		local param_type, result_type = self:unwrap_prim_function_type()
		context = ensure_context(context)
		local result_context = context
		local param_is_tuple_type, param_decls = param_type:as_prim_tuple_type()
		local ok, param_name, param_annotation, result_body, result_anchor = result_type:as_annotated_lambda()
		if not ok then
			error("override_pretty: inferrable.prim_function_type: result_type must be a lambda")
		end
		result_context = result_context:append(param_name)
		local result_is_destructure, result_is_rename, param_names, result_body, result_context =
			inferrable_destructure_helper(result_body, result_context)
		if result_is_rename then
			param_name = param_names
			result_is_destructure = false
		end
		local result_is_tuple_type, result_decls = result_body:as_prim_tuple_type()

		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("inferrable.prim-\u{03A0} ")
		pp:unit(pp:_resetcolor())

		if param_is_tuple_type and result_is_destructure then
			local members = inferrable_tuple_type_flatten(param_decls, context)

			if #members == 0 then
				pp:unit(pp:_color())
				pp:unit("()")
				pp:unit(pp:_resetcolor())
			else
				tuple_type_helper(pp, members, param_names)
			end
		elseif result_is_destructure then
			-- tuple_elim on params but params aren't a tuple type???
			-- probably shouldn't happen, but here's a handler
			pp:unit(pp:_color())
			pp:unit("(")
			pp:unit(pp:_resetcolor())

			for i, name in param_names:ipairs() do
				if i > 1 then
					pp:unit(" ")
				end
				pp:unit(name)
			end

			pp:unit(pp:_color())
			pp:unit(") : ")
			pp:unit(pp:_resetcolor())

			pp:any(param_type, context)
		else
			pp:unit(param_name)

			pp:unit(pp:_color())
			pp:unit(" : ")
			pp:unit(pp:_resetcolor())

			pp:any(param_type, context)
		end

		pp:unit(pp:_color())
		pp:unit(" -> ")
		pp:unit(pp:_resetcolor())

		if result_is_tuple_type then
			local members = inferrable_tuple_type_flatten(result_decls, result_context)

			if #members == 0 then
				pp:unit(pp:_color())
				pp:unit("()")
				pp:unit(pp:_resetcolor())
			else
				tuple_type_helper(pp, members)
			end
		else
			pp:any(result_body, result_context)
		end

		pp:_exit()
	end,
}

-- typed terms have been typechecked but do not store their type internally
typed_term:define_enum("typed", {
	{ "bound_variable", { "index", gen.builtin_number } },
	{ "literal", { "literal_value", value } },
	{ "lambda", {
		"param_name",
		gen.builtin_string,
		"body",
		typed_term,
	} },
	{
		"pi",
		{
			"param_type",
			typed_term,
			"param_info",
			typed_term,
			"result_type",
			typed_term,
			"result_info",
			typed_term,
		},
	},
	{ "application", {
		"f",
		typed_term,
		"arg",
		typed_term,
	} },
	{ "let", {
		"name",
		gen.builtin_string,
		"expr",
		typed_term,
		"body",
		typed_term,
	} },
	{ "level_type" },
	{ "level0" },
	{ "level_suc", { "previous_level", typed_term } },
	{ "level_max", {
		"level_a",
		typed_term,
		"level_b",
		typed_term,
	} },
	{ "star", { "level", gen.builtin_number } },
	{ "prop", { "level", gen.builtin_number } },
	{ "tuple_cons", { "elements", array(typed_term) } },
	--{"tuple_extend", {"base", typed_term, "fields", array(typed_term)}}, -- maybe?
	{
		"tuple_elim",
		{
			"names",
			array(gen.builtin_string),
			"subject",
			typed_term,
			"length",
			gen.builtin_number,
			"body",
			typed_term,
		},
	},
	{ "tuple_element_access", {
		"subject",
		typed_term,
		"index",
		gen.builtin_number,
	} },
	{ "tuple_type", { "definition", typed_term } },
	{ "record_cons", { "fields", map(gen.builtin_string, typed_term) } },
	{ "record_extend", {
		"base",
		typed_term,
		"fields",
		map(gen.builtin_string, typed_term),
	} },
	{
		"record_elim",
		{
			"subject",
			typed_term,
			"field_names",
			array(gen.builtin_string),
			"body",
			typed_term,
		},
	},
	--TODO record elim
	{ "enum_cons", {
		"constructor",
		gen.builtin_string,
		"arg",
		typed_term,
	} },
	{ "enum_elim", {
		"subject",
		typed_term,
		"mechanism",
		typed_term,
	} },
	{ "enum_rec_elim", {
		"subject",
		typed_term,
		"mechanism",
		typed_term,
	} },
	{ "object_cons", { "methods", map(gen.builtin_string, typed_term) } },
	{ "object_corec_cons", { "methods", map(gen.builtin_string, typed_term) } },
	{ "object_elim", {
		"subject",
		typed_term,
		"mechanism",
		typed_term,
	} },
	{ "operative_cons", { "userdata", typed_term } },
	{ "operative_type_cons", {
		"handler",
		typed_term,
		"userdata_type",
		typed_term,
	} },
	{ "prim_tuple_cons", { "elements", array(typed_term) } }, -- prim
	{
		"prim_user_defined_type_cons",
		{
			"id",
			prim_user_defined_id,
			"family_args",
			array(typed_term), -- prim
		},
	},
	{ "prim_tuple_type", { "decls", typed_term } }, -- just like an ordinary tuple type but can only hold prims
	{
		"prim_function_type",
		{
			"param_type",
			typed_term, -- must be a prim_tuple_type
			-- primitive functions can only have explicit arguments
			"result_type",
			typed_term, -- must be a prim_tuple_type
			-- primitive functions can only be pure for now
		},
	},
	{ "prim_wrapped_type", { "type", typed_term } },
	{ "prim_unstrict_wrapped_type", { "type", typed_term } },
	{ "prim_wrap", { "content", typed_term } },
	{ "prim_unwrap", { "container", typed_term } },
	{ "prim_unstrict_wrap", { "content", typed_term } },
	{ "prim_unstrict_unwrap", { "container", typed_term } },
	{ "prim_user_defined_type", {
		"id",
		prim_user_defined_id,
		"family_args",
		array(typed_term),
	} },
	{ "prim_if", {
		"subject",
		typed_term,
		"consequent",
		typed_term,
		"alternate",
		typed_term,
	} },
	{ "prim_intrinsic", {
		"source",
		typed_term,
		"anchor",
		gen.anchor_type,
	} },
})

-- the only difference compared to inferrable_let_or_tuple_elim is length
local function typed_let_or_tuple_elim(pp, term, context)
	pp:_enter()

	local name, expr, names, subject, length
	while true do
		if term:is_let() then
			name, expr, term = term:unwrap_let()

			-- rear-loading prefix to cheaply handle first loop not needing prefix
			pp:unit(pp:_color())
			pp:unit("typed.let ")
			pp:unit(pp:_resetcolor())
			context = let_helper(pp, name, expr, context)
			pp:unit("\n")
			pp:_prefix()
		elseif term:is_tuple_elim() then
			names, subject, length, term = term:unwrap_tuple_elim()

			pp:unit(pp:_color())
			pp:unit("typed.let ")
			pp:unit(pp:_resetcolor())
			context = tuple_elim_helper(pp, names, subject, context)
			pp:unit("\n")
			pp:_prefix()
		else
			break
		end
	end

	pp:any(term, context)

	pp:_exit()
end
-- the only difference compared to inferrable_destructure_helper is length
local function typed_destructure_helper(term, context)
	if term:is_let() then
		-- destructuring with a let effectively just renames the parameter
		-- thus it's usually superfluous to write code like this
		-- and probably unwise to elide the let
		-- but some operatives that are generic over lets and tuple-elims do this
		-- e.g. forall, lambda
		-- so we pretty this anyway
		local name, expr, body = term:unwrap_let()
		local ok, index = expr:as_bound_variable()
		local is_destructure = ok and index == #context
		if is_destructure then
			context = context:append(name)
			return is_destructure, true, name, body, context
		end
	elseif term:is_tuple_elim() then
		local names, subject, length, body = term:unwrap_tuple_elim()
		local ok, index = subject:as_bound_variable()
		local is_destructure = ok and index == #context
		if is_destructure then
			for i, name in names:ipairs() do
				context = context:append(name)
			end
			return is_destructure, false, names, body, context
		end
	end
	return false, false, nil, term, context
end
-- mostly the same as inferrable_tuple_type_flatten
local function typed_tuple_type_flatten(definition, context)
	local constructor, arg = definition:unwrap_enum_cons()
	if constructor == "empty" then
		return {}, 0
	elseif constructor == "cons" then
		local elements = arg:unwrap_tuple_cons()
		local definition = elements[1]
		local f = elements[2]
		local ok, param_name, body = f:as_lambda()
		if not ok then
			error("override_pretty: typed.tuple_type: tuple decl must be a lambda")
		end
		local inner_context = context:append(param_name)
		local is_destructure, is_rename, names, body, inner_context = typed_destructure_helper(body, inner_context)
		local prev, n = typed_tuple_type_flatten(definition, context)
		n = n + 1
		prev[n] = { names, body, inner_context }
		return prev, n
	else
		error("override_pretty: typed.tuple_type: unknown tuple type data constructor")
	end
end
local typed_term_override_pretty = {
	-- copypaste of inferrable.bound_variable
	bound_variable = function(self, pp, context)
		local index = self:unwrap_bound_variable()
		context = ensure_context(context)

		pp:_enter()

		if #context >= index then
			pp:unit(context:get_name(index))
		else
			-- TODO: warn on context too short?
			pp:unit(pp:_color())
			pp:unit("typed.bound_variable(")
			pp:unit(pp:_resetcolor())

			pp:unit(tostring(index))

			pp:unit(pp:_color())
			pp:unit(")")
			pp:unit(pp:_resetcolor())
		end

		pp:_exit()
	end,
	literal = function(self, pp)
		local literal_value = self:unwrap_literal()
		pp:any(literal_value)
	end,
	-- some similarities to inferrable.annotated_lambda
	lambda = function(self, pp, context)
		local param_name, body = self:unwrap_lambda()
		context = ensure_context(context)
		local inner_context = context:append(param_name)
		local is_destructure, is_rename, names, body, inner_context = typed_destructure_helper(body, inner_context)
		if is_rename then
			param_name = names
			is_destructure = false
		end

		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("typed.\u{03BB} ")
		pp:unit(pp:_resetcolor())

		if is_destructure then
			if #names == 0 then
				pp:unit(pp:_color())
				pp:unit("()")
				pp:unit(pp:_resetcolor())
			end

			for i, name in names:ipairs() do
				if i > 1 then
					pp:unit(" ")
				end
				pp:unit(name)
			end
		else
			pp:unit(param_name)
		end

		pp:unit(pp:_color())
		pp:unit(" ->")
		pp:unit(pp:_resetcolor())

		if body:is_let() or body:is_tuple_elim() then
			pp:unit("\n")
			pp:_indent()
			pp:_prefix()
			pp:any(body, inner_context)
			pp:_dedent()
		else
			pp:unit(" ")
			pp:any(body, inner_context)
		end

		pp:_exit()
	end,
	-- copypaste of inferrable.pi
	pi = function(self, pp, context)
		-- extracting parameter names from the destructure of the result
		-- so that we get the name of the last parameter
		-- name of the last result is still lost
		local param_type, param_info, result_type, result_info = self:unwrap_pi()
		context = ensure_context(context)
		local result_context = context
		local param_is_tuple_type, param_decls = as_any_tuple_type(param_type)
		local ok, param_name, result_body = result_type:as_lambda()
		if not ok then
			error("override_pretty: typed.pi: result_type must be a lambda")
		end
		result_context = result_context:append(param_name)
		local result_is_destructure, result_is_rename, param_names, result_body, result_context =
			typed_destructure_helper(result_body, result_context)
		if result_is_rename then
			param_name = param_names
			result_is_destructure = false
		end
		local result_is_tuple_type, result_decls = as_any_tuple_type(result_body)

		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("typed.\u{03A0} ")
		pp:unit(pp:_resetcolor())

		if param_is_tuple_type and result_is_destructure then
			local members = typed_tuple_type_flatten(param_decls, context)

			if #members == 0 then
				pp:unit(pp:_color())
				pp:unit("()")
				pp:unit(pp:_resetcolor())
			else
				tuple_type_helper(pp, members, param_names)
			end
		elseif result_is_destructure then
			-- tuple_elim on params but params aren't a tuple type???
			-- probably shouldn't happen, but here's a handler
			pp:unit(pp:_color())
			pp:unit("(")
			pp:unit(pp:_resetcolor())

			for i, name in param_names:ipairs() do
				if i > 1 then
					pp:unit(" ")
				end
				pp:unit(name)
			end

			pp:unit(pp:_color())
			pp:unit(") : ")
			pp:unit(pp:_resetcolor())

			pp:any(param_type, context)
		else
			pp:unit(param_name)

			pp:unit(pp:_color())
			pp:unit(" : ")
			pp:unit(pp:_resetcolor())

			pp:any(param_type, context)
		end

		pp:unit(pp:_color())
		pp:unit(" -> ")
		pp:unit(pp:_resetcolor())

		if result_is_tuple_type then
			local members = typed_tuple_type_flatten(result_decls, result_context)

			if #members == 0 then
				pp:unit(pp:_color())
				pp:unit("()")
				pp:unit(pp:_resetcolor())
			else
				tuple_type_helper(pp, members)
			end
		else
			pp:any(result_body, result_context)
		end

		pp:_exit()
	end,
	-- copypaste from inferrable.application
	application = function(self, pp, context)
		local f, arg = self:unwrap_application()
		context = ensure_context(context)

		-- handle nested applications
		local function application_inner(f, arg)
			local f_is_application, f_f, f_arg = f:as_application()
			local f_is_bound_variable, f_index = f:as_bound_variable()

			pp:_enter()

			-- print pretty on certain conditions, or fall back to apply()
			if
				(f_is_application or (f_is_bound_variable and #context >= f_index))
				and (arg:is_tuple_cons() or arg:is_prim_tuple_cons())
			then
				if f_is_application then
					application_inner(f_f, f_arg)
				else
					pp:unit(context:get_name(f_index))
				end

				local ok, elements = arg:as_tuple_cons()
				elements = ok and elements or arg:unwrap_prim_tuple_cons()

				pp:unit(pp:_color())
				pp:unit("(")
				pp:unit(pp:_resetcolor())

				for i, arg in ipairs(elements) do
					if i > 1 then
						pp:unit(pp:_color())
						pp:unit(", ")
						pp:unit(pp:_resetcolor())
					end

					pp:any(arg, context)
				end

				pp:unit(pp:_color())
				pp:unit(")")
				pp:unit(pp:_resetcolor())
			else
				-- if we're here then the args are probably horrible
				-- add some newlines
				pp:unit(pp:_color())
				pp:unit("typed.apply(")
				pp:unit(pp:_resetcolor())
				pp:unit("\n")

				pp:_indent()

				pp:_prefix()
				pp:any(f, context)
				pp:unit(pp:_color())
				pp:unit(",")
				pp:unit(pp:_resetcolor())
				pp:unit("\n")

				pp:_prefix()
				pp:any(arg, context)
				pp:unit("\n")

				pp:_dedent()

				pp:_prefix()
				pp:unit(pp:_color())
				pp:unit(")")
				pp:unit(pp:_resetcolor())
			end

			pp:_exit()
		end

		application_inner(f, arg)
	end,
	let = function(self, pp, context)
		context = ensure_context(context)
		typed_let_or_tuple_elim(pp, self, context)
	end,
	tuple_elim = function(self, pp, context)
		context = ensure_context(context)
		typed_let_or_tuple_elim(pp, self, context)
	end,
	-- some copypaste from typed.application
	tuple_element_access = function(self, pp, context)
		local subject, index = self:unwrap_tuple_element_access()
		context = ensure_context(context)
		local subject_is_bound_variable, subject_index = subject:as_bound_variable()

		if subject_is_bound_variable and #context >= subject_index then
			pp:_enter()

			pp:unit(context:get_name(subject_index))

			pp:unit(pp:_color())
			pp:unit(".")
			pp:unit(pp:_resetcolor())

			pp:unit(tostring(index))

			pp:_exit()
		else
			pp:record("typed.tuple_element_access", { { "subject", subject }, { "index", index } }, context)
		end
	end,
	tuple_type = function(self, pp, context)
		local definition = self:unwrap_tuple_type()
		context = ensure_context(context)
		local members = typed_tuple_type_flatten(definition, context)

		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("typed.tuple_type[")
		pp:unit(pp:_resetcolor())

		tuple_type_helper(pp, members)

		pp:unit(pp:_color())
		pp:unit("]")
		pp:unit(pp:_resetcolor())

		pp:_exit()
	end,
	prim_tuple_type = function(self, pp, context)
		local decls = self:unwrap_prim_tuple_type()
		context = ensure_context(context)
		local members = typed_tuple_type_flatten(decls, context)

		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("typed.prim_tuple_type[")
		pp:unit(pp:_resetcolor())

		tuple_type_helper(pp, members)

		pp:unit(pp:_color())
		pp:unit("]")
		pp:unit(pp:_resetcolor())

		pp:_exit()
	end,
	-- copypaste of inferrable.prim_function_type
	prim_function_type = function(self, pp, context)
		local param_type, result_type = self:unwrap_prim_function_type()
		context = ensure_context(context)
		local result_context = context
		local param_is_tuple_type, param_decls = param_type:as_prim_tuple_type()
		local ok, param_name, result_body = result_type:as_lambda()
		if not ok then
			error("override_pretty: typed.prim_function_type: result_type must be a lambda")
		end
		result_context = result_context:append(param_name)
		local result_is_destructure, result_is_rename, param_names, result_body, result_context =
			typed_destructure_helper(result_body, result_context)
		if result_is_rename then
			param_name = param_names
			result_is_destructure = false
		end
		local result_is_tuple_type, result_decls = result_body:as_prim_tuple_type()

		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("typed.prim-\u{03A0} ")
		pp:unit(pp:_resetcolor())

		if param_is_tuple_type and result_is_destructure then
			local members = typed_tuple_type_flatten(param_decls, context)

			if #members == 0 then
				pp:unit(pp:_color())
				pp:unit("()")
				pp:unit(pp:_resetcolor())
			else
				tuple_type_helper(pp, members, param_names)
			end
		elseif result_is_destructure then
			-- tuple_elim on params but params aren't a tuple type???
			-- probably shouldn't happen, but here's a handler
			pp:unit(pp:_color())
			pp:unit("(")
			pp:unit(pp:_resetcolor())

			for i, name in param_names:ipairs() do
				if i > 1 then
					pp:unit(" ")
				end
				pp:unit(name)
			end

			pp:unit(pp:_color())
			pp:unit(") : ")
			pp:unit(pp:_resetcolor())

			pp:any(param_type, context)
		else
			pp:unit(param_name)

			pp:unit(pp:_color())
			pp:unit(" : ")
			pp:unit(pp:_resetcolor())

			pp:any(param_type, context)
		end

		pp:unit(pp:_color())
		pp:unit(" -> ")
		pp:unit(pp:_resetcolor())

		if result_is_tuple_type then
			local members = typed_tuple_type_flatten(result_decls, result_context)

			if #members == 0 then
				pp:unit(pp:_color())
				pp:unit("()")
				pp:unit(pp:_resetcolor())
			else
				tuple_type_helper(pp, members)
			end
		else
			pp:any(result_body, result_context)
		end

		pp:_exit()
	end,
	prim_intrinsic = function(self, pp)
		local source, anchor = self:unwrap_prim_intrinsic()
		local ok, source_val = source:as_literal()
		if not ok then
			error("override_pretty: typed.prim_intrinsic: source must be a literal prim string")
		end
		local ok, source_text = source_val:as_prim()
		if not ok or type(source_text) ~= "string" then
			error("override_pretty: typed.prim_intrinsic: source must be a literal prim string")
		end

		-- trim initial newlines
		-- get first line
		-- ellipsize further lines
		local source_print = string.gsub(source_text, "^%c*(%C*)(.*)", function(visible, rest)
			if #rest > 0 then
				return visible .. " ..."
			else
				return visible
			end
		end)

		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("typed.prim_intrinsic ")
		pp:unit(pp:_resetcolor())

		pp:any(source_print)

		pp:_exit()
	end,
}

local unique_id = gen.declare_foreign(function(val)
	return type(val) == "table"
end)

placeholder_debug:define_record("placeholder_debug", { "name", gen.builtin_string, "anchor", gen.anchor_type })

free:define_enum("free", {
	{ "metavariable", { "metavariable", metavariable_type } },
	{ "placeholder", {
		"index",
		gen.builtin_number,
		"debug",
		placeholder_debug,
	} },
	{ "unique", { "id", unique_id } },
	-- TODO: axiom
})

-- implicit arguments are filled in through unification
-- e.g. fn append(t : star(0), n : nat, xs : Array(t, n), val : t) -> Array(t, n+1)
--      t and n can be implicit, given the explicit argument xs, as they're filled in by unification
---@module "./types/visibility"
local visibility = gen.declare_enum("visibility", {
	{ "explicit" },
	{ "implicit" },
})
-- whether a function is effectful or pure
-- an effectful function must return a monad
-- calling an effectful function implicitly inserts a monad bind between the
-- function return and getting the result of the call
---@module "./types/purity"
local purity = gen.declare_enum("purity", {
	{ "effectful" },
	{ "pure" },
})

---@module "./types/result_info"
local result_info = gen.declare_record("result_info", { "purity", purity })

-- values must always be constructed in their simplest form, that cannot be reduced further.
-- their format must enforce this invariant.
-- e.g. it must be impossible to construct "2 + 2"; it should be constructed in reduced form "4".
-- values can contain neutral values, which represent free variables and stuck operations.
-- stuck operations are those that are blocked from further evaluation by a neutral value.
-- therefore neutral values must always contain another neutral value or a free variable.
-- their format must enforce this invariant.
-- e.g. it's possible to construct the neutral value "x + 2"; "2" is not neutral, but "x" is.
-- values must all be finite in size and must not have loops.
-- i.e. destructuring values always (eventually) terminates.
value:define_enum("value", {
	-- explicit, implicit,
	{ "visibility_type" },
	{ "visibility", { "visibility", visibility } },
	-- info about the parameter (is it implicit / what are the usage restrictions?)
	-- quantity/visibility should be restricted to free or (quantity/visibility) rather than any value
	{ "param_info_type" },
	{ "param_info", { "visibility", value } },
	-- whether or not a function is effectful /
	-- for a function returning a monad do i have to be called in an effectful context or am i pure
	{ "result_info_type" },
	{ "result_info", { "result_info", result_info } },
	{
		"pi",
		{
			"param_type",
			value,
			"param_info",
			value, -- param_info
			"result_type",
			value, -- closure from input -> result
			"result_info",
			value, -- result_info
		},
	},
	-- closure is a type that contains a typed term corresponding to the body
	-- and a runtime context representng the bound context where the closure was created
	{
		"closure",
		{
			"param_name",
			gen.builtin_string,
			"code",
			typed_term,
			"capture",
			runtime_context_type,
		},
	},

	-- metaprogramming stuff
	-- TODO: add types of terms, and type indices
	-- NOTE: we're doing this through prims instead
	--{"syntax_value", {"syntax", metalang.constructed_syntax_type}},
	--{"syntax_type"},
	--{"matcher_value", {"matcher", metalang.matcher_type}},
	--{"matcher_type", {"result_type", value}},
	--{"reducer_value", {"reducer", metalang.reducer_type}},
	--{"environment_value", {"environment", environment_type}},
	--{"environment_type"},
	--{"checkable_term", {"checkable_term", checkable_term}},
	--{"inferrable_term", {"inferrable_term", inferrable_term}},
	--{"inferrable_term_type"},
	--{"typed_term", {"typed_term", typed_term}},
	--{"typechecker_monad_value", }, -- TODO
	--{"typechecker_monad_type", {"wrapped_type", value}},
	{ "name_type" },
	{ "name", { "name", gen.builtin_string } },
	{ "operative_value", { "userdata", value } },
	{ "operative_type", {
		"handler",
		value,
		"userdata_type",
		value,
	} },

	-- ordinary data
	{ "tuple_value", { "elements", array(value) } },
	{ "tuple_type", { "decls", value } },
	{ "tuple_defn_type", { "universe", value } },
	{ "enum_value", {
		"constructor",
		gen.builtin_string,
		"arg",
		value,
	} },
	{ "enum_type", { "decls", value } },
	{ "enum_defn_type", { "universe", value } },
	{ "record_value", { "fields", map(gen.builtin_string, value) } },
	{ "record_type", { "decls", value } },
	{ "record_defn_type", { "universe", value } },
	{ "record_extend_stuck", {
		"base",
		neutral_value,
		"extension",
		map(gen.builtin_string, value),
	} },
	{ "object_value", {
		"methods",
		map(gen.builtin_string, typed_term),
		"capture",
		runtime_context_type,
	} },
	{ "object_type", { "decls", value } },
	{ "level_type" },
	{ "number_type" },
	{ "number", { "number", gen.builtin_number } },
	{ "level", { "level", gen.builtin_number } },
	{ "star", { "level", gen.builtin_number } },
	{ "prop", { "level", gen.builtin_number } },
	{ "neutral", { "neutral", neutral_value } },

	-- foreign data
	{ "prim", { "primitive_value", gen.any_lua_type } },
	{ "prim_type_type" },
	{ "prim_number_type" },
	{ "prim_bool_type" },
	{ "prim_string_type" },
	{
		"prim_function_type",
		{
			"param_type",
			value, -- must be a prim_tuple_type
			-- primitive functions can only have explicit arguments
			"result_type",
			value, -- must be a prim_tuple_type
			-- primitive functions can only be pure for now
		},
	},
	{ "prim_wrapped_type", { "type", value } },
	{ "prim_unstrict_wrapped_type", { "type", value } },
	{ "prim_user_defined_type", {
		"id",
		prim_user_defined_id,
		"family_args",
		array(value),
	} },
	{ "prim_nil_type" },
	--NOTE: prim_tuple is not considered a prim type because it's not a first class value in lua.
	{ "prim_tuple_value", { "elements", array(gen.any_lua_type) } },
	{ "prim_tuple_type", { "decls", value } }, -- just like an ordinary tuple type but can only hold prims

	-- type of key and value of key -> type of the value
	-- {"prim_table_type"},
})

-- mostly the same as typed_tuple_type_flatten
-- differences:
-- - enum_value / tuple_value (as opposed to *_cons)
-- - closure instead of lambda
-- - context comes from closure
local function value_tuple_type_flatten(definition)
	local constructor, arg = definition:unwrap_enum_value()
	if constructor == "empty" then
		return {}, 0
	elseif constructor == "cons" then
		local elements = arg:unwrap_tuple_value()
		local definition = elements[1]
		local f = elements[2]
		local ok, param_name, code, capture = f:as_closure()
		if not ok then
			error("override_pretty: value.tuple_type: tuple decl must be a closure")
		end
		local context = ensure_context(capture)
		local inner_context = context:append(param_name)
		local is_destructure, is_rename, names, code, inner_context = typed_destructure_helper(code, inner_context)
		local prev, n = value_tuple_type_flatten(definition)
		n = n + 1
		prev[n] = { names, code, inner_context }
		return prev, n
	else
		error("override_pretty: value.tuple_type: unknown tuple type data constructor")
	end
end
local value_override_pretty = {
	-- copypaste of typed.pi
	pi = function(self, pp)
		local param_type, param_info, result_type, result_info = self:unwrap_pi()
		local param_is_tuple_type, param_decls = as_any_tuple_type(param_type)
		local ok, param_name, result_code, result_capture = result_type:as_closure()
		if not ok then
			error("override_pretty: value.pi: result_type must be a closure")
		end
		local result_context = ensure_context(result_capture)
		result_context = result_context:append(param_name)
		local result_is_destructure, result_is_rename, param_names, result_code, result_context =
			typed_destructure_helper(result_code, result_context)
		if result_is_rename then
			param_name = param_names
			result_is_destructure = false
		end
		local result_is_tuple_type, result_decls = as_any_tuple_type(result_code)

		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("value.\u{03A0} ")
		pp:unit(pp:_resetcolor())

		if param_is_tuple_type and result_is_destructure then
			local members = value_tuple_type_flatten(param_decls, context)

			if #members == 0 then
				pp:unit(pp:_color())
				pp:unit("()")
				pp:unit(pp:_resetcolor())
			else
				tuple_type_helper(pp, members, param_names)
			end
		elseif result_is_destructure then
			-- tuple_elim on params but params aren't a tuple type???
			-- probably shouldn't happen, but here's a handler
			pp:unit(pp:_color())
			pp:unit("(")
			pp:unit(pp:_resetcolor())

			for i, name in param_names:ipairs() do
				if i > 1 then
					pp:unit(" ")
				end
				pp:unit(name)
			end

			pp:unit(pp:_color())
			pp:unit(") : ")
			pp:unit(pp:_resetcolor())

			pp:any(param_type, context)
		else
			pp:unit(param_name)

			pp:unit(pp:_color())
			pp:unit(" : ")
			pp:unit(pp:_resetcolor())

			pp:any(param_type, context)
		end

		pp:unit(pp:_color())
		pp:unit(" -> ")
		pp:unit(pp:_resetcolor())

		if result_is_tuple_type then
			local members = typed_tuple_type_flatten(result_decls, result_context)

			if #members == 0 then
				pp:unit(pp:_color())
				pp:unit("()")
				pp:unit(pp:_resetcolor())
			else
				tuple_type_helper(pp, members)
			end
		else
			pp:any(result_code, result_context)
		end

		pp:_exit()
	end,
	-- the only difference compared to typed.lambda is context coming from within the closure
	closure = function(self, pp)
		local param_name, code, capture = self:unwrap_closure()
		local context = ensure_context(capture)
		local inner_context = context:append(param_name)
		local is_destructure, is_rename, names, code, inner_context = typed_destructure_helper(code, inner_context)
		if is_rename then
			param_name = names
			is_destructure = false
		end

		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("value.closure ")
		pp:unit(pp:_resetcolor())

		if is_destructure then
			if #names == 0 then
				pp:unit(pp:_color())
				pp:unit("()")
				pp:unit(pp:_resetcolor())
			end

			for i, name in names:ipairs() do
				if i > 1 then
					pp:unit(" ")
				end
				pp:unit(name)
			end
		else
			pp:unit(param_name)
		end

		pp:unit(pp:_color())
		pp:unit(" ->")
		pp:unit(pp:_resetcolor())

		if code:is_let() or code:is_tuple_elim() then
			pp:unit("\n")
			pp:_indent()
			pp:_prefix()
			pp:any(code, inner_context)
			pp:_dedent()
		else
			pp:unit(" ")
			pp:any(code, inner_context)
		end

		pp:_exit()
	end,
	tuple_type = function(self, pp)
		local decls = self:unwrap_tuple_type()
		local members = value_tuple_type_flatten(decls)

		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("value.tuple_type[")
		pp:unit(pp:_resetcolor())

		tuple_type_helper(pp, members)

		pp:unit(pp:_color())
		pp:unit("]")
		pp:unit(pp:_resetcolor())

		pp:_exit()
	end,
	-- copypaste of typed.prim_function_type
	prim_function_type = function(self, pp)
		local param_type, result_type = self:unwrap_prim_function_type()
		local param_is_tuple_type, param_decls = param_type:as_prim_tuple_type()
		local ok, param_name, result_code, result_capture = result_type:as_closure()
		if not ok then
			--error("override_pretty: value.prim_function_type: result_type must be a closure")
			-- allow printing cursed things that contain manually-written (broken) prim-func-types
			pp:unit("<BROKEN prim_function_type>")
			return
		end
		local result_context = ensure_context(result_capture)
		result_context = result_context:append(param_name)
		local result_is_destructure, result_is_rename, param_names, result_code, result_context =
			typed_destructure_helper(result_code, result_context)
		if result_is_rename then
			param_name = param_names
			result_is_destructure = false
		end
		local result_is_tuple_type, result_decls = result_code:as_prim_tuple_type()

		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("value.prim-\u{03A0} ")
		pp:unit(pp:_resetcolor())

		if param_is_tuple_type and result_is_destructure then
			local members = value_tuple_type_flatten(param_decls, context)

			if #members == 0 then
				pp:unit(pp:_color())
				pp:unit("()")
				pp:unit(pp:_resetcolor())
			else
				tuple_type_helper(pp, members, param_names)
			end
		elseif result_is_destructure then
			-- tuple_elim on params but params aren't a tuple type???
			-- probably shouldn't happen, but here's a handler
			pp:unit(pp:_color())
			pp:unit("(")
			pp:unit(pp:_resetcolor())

			for i, name in param_names:ipairs() do
				if i > 1 then
					pp:unit(" ")
				end
				pp:unit(name)
			end

			pp:unit(pp:_color())
			pp:unit(") : ")
			pp:unit(pp:_resetcolor())

			pp:any(param_type, context)
		else
			pp:unit(param_name)

			pp:unit(pp:_color())
			pp:unit(" : ")
			pp:unit(pp:_resetcolor())

			pp:any(param_type, context)
		end

		pp:unit(pp:_color())
		pp:unit(" -> ")
		pp:unit(pp:_resetcolor())

		if result_is_tuple_type then
			local members = typed_tuple_type_flatten(result_decls, result_context)

			if #members == 0 then
				pp:unit(pp:_color())
				pp:unit("()")
				pp:unit(pp:_resetcolor())
			else
				tuple_type_helper(pp, members)
			end
		else
			pp:any(result_code, result_context)
		end

		pp:_exit()
	end,
	prim_tuple_type = function(self, pp)
		local decls = self:unwrap_prim_tuple_type()
		local members = value_tuple_type_flatten(decls)

		pp:_enter()

		pp:unit(pp:_color())
		pp:unit("value.prim_tuple_type[")
		pp:unit(pp:_resetcolor())

		tuple_type_helper(pp, members)

		pp:unit(pp:_color())
		pp:unit("]")
		pp:unit(pp:_resetcolor())

		pp:_exit()
	end,
}

neutral_value:define_enum("neutral_value", {
	-- fn(free_value) and table of functions eg free.metavariable(metavariable)
	-- value should be constructed w/ free.something()
	{ "free", { "free", free } },
	{ "application_stuck", {
		"f",
		neutral_value,
		"arg",
		value,
	} },
	{ "enum_elim_stuck", {
		"mechanism",
		value,
		"subject",
		neutral_value,
	} },
	{ "enum_rec_elim_stuck", {
		"handler",
		value,
		"subject",
		neutral_value,
	} },
	{ "object_elim_stuck", {
		"mechanism",
		value,
		"subject",
		neutral_value,
	} },
	{ "tuple_element_access_stuck", {
		"subject",
		neutral_value,
		"index",
		gen.builtin_number,
	} },
	{ "record_field_access_stuck", {
		"subject",
		neutral_value,
		"field_name",
		gen.builtin_string,
	} },
	{ "prim_application_stuck", {
		"function",
		gen.any_lua_type,
		"arg",
		neutral_value,
	} },
	{
		"prim_tuple_stuck",
		{
			"leading",
			array(gen.any_lua_type),
			"stuck_element",
			neutral_value,
			"trailing",
			array(value), -- either primitive or neutral
		},
	},
	{ "prim_if_stuck", {
		"subject",
		neutral_value,
		"consequent",
		value,
		"alternate",
		value,
	} },
	{ "prim_intrinsic_stuck", {
		"source",
		neutral_value,
		"anchor",
		gen.anchor_type,
	} },
	{ "prim_wrap_stuck", { "content", neutral_value } },
	{ "prim_unwrap_stuck", { "container", neutral_value } },
})

local prim_syntax_type = value.prim_user_defined_type({ name = "syntax" }, array(value)())
local prim_environment_type = value.prim_user_defined_type({ name = "environment" }, array(value)())
local prim_typed_term_type = value.prim_user_defined_type({ name = "typed_term" }, array(value)())
local prim_goal_type = value.prim_user_defined_type({ name = "goal" }, array(value)())
local prim_inferrable_term_type = value.prim_user_defined_type({ name = "inferrable_term" }, array(value)())
-- return ok, err
local prim_lua_error_type = value.prim_user_defined_type({ name = "lua_error_type" }, array(value)())

local function tup_val(...)
	return value.tuple_value(array(value)(...))
end
local function cons(...)
	return value.enum_value("cons", tup_val(...))
end
local empty = value.enum_value("empty", tup_val())
local unit_type = value.tuple_type(empty)
local unit_val = tup_val()

for _, deriver in ipairs { derivers.as, derivers.eq, derivers.diff } do
	checkable_term:derive(deriver)
	inferrable_term:derive(deriver)
	typed_term:derive(deriver)
	visibility:derive(deriver)
	free:derive(deriver)
	value:derive(deriver)
	neutral_value:derive(deriver)
	binding:derive(deriver)
	expression_goal:derive(deriver)
	placeholder_debug:derive(deriver)
	purity:derive(deriver)
	result_info:derive(deriver)
end

checkable_term:derive(derivers.pretty_print, checkable_term_override_pretty)
inferrable_term:derive(derivers.pretty_print, inferrable_term_override_pretty)
typed_term:derive(derivers.pretty_print, typed_term_override_pretty)
visibility:derive(derivers.pretty_print)
free:derive(derivers.pretty_print)
value:derive(derivers.pretty_print, value_override_pretty)
neutral_value:derive(derivers.pretty_print)
binding:derive(derivers.pretty_print, binding_override_pretty)
expression_goal:derive(derivers.pretty_print)
placeholder_debug:derive(derivers.pretty_print)
purity:derive(derivers.pretty_print)
result_info:derive(derivers.pretty_print)

--[[
local tuple_defn = value.enum_value("variant",
	tup_val(
		value.enum_value("variant",
			tup_val(
				value.enum_value("empty", tup_val()),
				value.prim "element",
				value.closure()
			)
		),


	)
)]]

local terms = {
	typechecker_state = typechecker_state, -- fn (constructor)
	checkable_term = checkable_term, -- {}
	inferrable_term = inferrable_term, -- {}
	typed_term = typed_term, -- {}
	free = free,
	visibility = visibility,
	purity = purity,
	result_info = result_info,
	value = value,
	neutral_value = neutral_value,
	binding = binding,
	expression_goal = expression_goal,
	prim_syntax_type = prim_syntax_type,
	prim_environment_type = prim_environment_type,
	prim_typed_term_type = prim_typed_term_type,
	prim_goal_type = prim_goal_type,
	prim_inferrable_term_type = prim_inferrable_term_type,
	prim_lua_error_type = prim_lua_error_type,
	unit_val = unit_val,
	unit_type = unit_type,

	runtime_context = runtime_context,
	typechecking_context = typechecking_context,
	module_mt = module_mt,
	runtime_context_type = runtime_context_type,
	typechecking_context_type = typechecking_context_type,
}
local internals_interface = require "./internals-interface"
internals_interface.terms = terms
return terms
