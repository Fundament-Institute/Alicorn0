local terms = require "./terms"
local metalanguage = require "./metalanguage"
local U = require "./alicorn-utils"
local runtime_context = terms.runtime_context
--local new_typechecking_context = terms.typechecking_context
--local checkable_term = terms.checkable_term
--local inferrable_term = terms.inferrable_term
local typed_term = terms.typed_term
local free = terms.free
local visibility = terms.visibility
local purity = terms.purity
local result_info = terms.result_info
local value = terms.value
local neutral_value = terms.neutral_value
local prim_syntax_type = terms.prim_syntax_type
local prim_environment_type = terms.prim_environment_type
local prim_typed_term_type = terms.prim_typed_term_type
local prim_goal_type = terms.prim_goal_type
local prim_inferrable_term_type = terms.prim_inferrable_term_type

local gen = require "./terms-generators"
local map = gen.declare_map
local string_typed_map = map(gen.builtin_string, typed_term)
local string_value_map = map(gen.builtin_string, value)
local array = gen.declare_array
local typed_array = array(typed_term)
local value_array = array(value)
local primitive_array = array(gen.any_lua_type)
local usage_array = array(gen.builtin_number)
local string_array = array(gen.builtin_string)

local internals_interface = require "./internals-interface"

local param_info_explicit = value.param_info(value.visibility(visibility.explicit))
local result_info_pure = value.result_info(result_info(purity.pure))

--local derivers = require "./derivers"
--local traits = require "./traits"
local OMEGA = 10
local typechecker_state
local evaluate, infer, check, apply_value
local name_array = gen.declare_array(gen.builtin_string)
local typed = terms.typed_term

---@param luafunc function
---@param parameters Array -- example usage: name_array("#wrap-TODO1", "#wrap-TODO2")
---@return value
local function luatovalue(luafunc, parameters)
	local len = parameters:len()
	local new_body = typed_array()

	for i = 1, len do
		new_body:append(typed.bound_variable(i + 1))
	end

	return value.closure(
		"#args",
		typed.application(
			typed.literal(value.prim(luafunc)),
			typed.tuple_elim(parameters, typed.bound_variable(1), len, typed.prim_tuple_cons(new_body))
		),
		runtime_context()
	)
end

---@param srel SubtypeRelation
---@return SubtypeRelation
local function FunctionRelation(srel)
	return {
		srel = srel,
		Rel = luatovalue(function(a, b) end, name_array("a", "b")),
		refl = luatovalue(function(a) end, name_array("a")),
		antisym = luatovalue(function(a, b, r1, r2) end, name_array("a", "b", "r1", "r2")),
		constrain = luatovalue(function(val, use)
			local u = value.neutral(neutral_value.free(free.unique({})))

			local applied_val = apply_value(val, u)
			local applied_use = apply_value(use, u)

			--  Call the constrain of our contained srel variable, which will throw an error if it fails
			local tuple_params = value_array(value.prim(applied_val), value.prim(applied_use))
			U.tag(
				"apply_value",
				{ applied_val, applied_use },
				apply_value,
				srel.constrain,
				value.tuple_value(tuple_params)
			)
		end, name_array("val", "use")),
	}
end
FunctionRelation = U.memoize(FunctionRelation)

---@type SubtypeRelation
local UniverseOmegaRelation

---@param onto Array
---@param with Array
local function add_arrays(onto, with)
	local olen = #onto
	for i, n in ipairs(with) do
		local x
		if i > olen then
			x = 0
		else
			x = onto[i]
		end
		onto[i] = x + n
	end
end

---make an alicorn function that returns the specified values
---@param v value
---@return value
local function const_combinator(v)
	return value.closure("#CONST_PARAM", typed_term.bound_variable(1), runtime_context():append(v))
end

---@param t value
---@return integer
local function get_level(t)
	-- TODO: this
	-- TODO: typecheck
	return 0
end

---@param val value an alicorn value
---@param mappings {[integer]: typed} the placeholder we are trying to get rid of by substituting
---@param context_len integer number of bindings in the runtime context already used - needed for closures
---@return typed a typed term
local function substitute_inner(val, mappings, context_len)
	if val:is_visibility_type() then
		return typed_term.literal(val)
	elseif val:is_visibility() then
		return typed_term.literal(val)
	elseif val:is_param_info_type() then
		return typed_term.literal(val)
	elseif val:is_param_info() then
		-- local visibility = val:unwrap_param_info()
		-- TODO: this needs to be evaluated properly because it contains a value
		return typed_term.literal(val)
	elseif val:is_result_info_type() then
		return typed_term.literal(val)
	elseif val:is_result_info() then
		return typed_term.literal(val)
	elseif val:is_pi() then
		local param_type, param_info, result_type, result_info = val:unwrap_pi()
		local param_type = substitute_inner(param_type, mappings, context_len)
		local param_info = substitute_inner(param_info, mappings, context_len)
		local result_type = substitute_inner(result_type, mappings, context_len)
		local result_info = substitute_inner(result_info, mappings, context_len)
		return typed_term.pi(param_type, param_info, result_type, result_info)
	elseif val:is_closure() then
		local param_name, code, capture = val:unwrap_closure()
		local unique = {}
		local arg = value.neutral(neutral_value.free(free.unique(unique)))
		val = apply_value(val, arg)
		--print("applied closure during substitution: (value term follows)")
		--print(val)

		-- Here we need to add the new arg placeholder to a map of things to substitute
		-- otherwise it would be left as a free.unique in the result
		mappings[unique] = typed_term.bound_variable(context_len + 1)
		local val_typed = substitute_inner(val, mappings, context_len + 1)

		-- FIXME: this results in more captures every time we substitute a closure ->
		--   can cause non-obvious memory leaks
		--   since we don't yet remove unused captures from closure value
		return typed_term.lambda(param_name, val_typed)
	elseif val:is_name_type() then
		return typed_term.literal(val)
	elseif val:is_name() then
		return typed_term.literal(val)
	elseif val:is_operative_value() then
		local userdata = val:unwrap_operative_value()
		local userdata = substitute_inner(userdata, mappings, context_len)
		return typed_term.operative_cons(userdata)
	elseif val:is_operative_type() then
		local handler, userdata_type = val:unwrap_operative_type()
		local typed_handler = substitute_inner(handler, mappings, context_len)
		local typed_userdata_type = substitute_inner(userdata_type, mappings, context_len)
		return typed_term.operative_type_cons(typed_handler, typed_userdata_type)
	elseif val:is_tuple_value() then
		local elems = val:unwrap_tuple_value()
		local res = typed_array()
		for _, v in ipairs(elems) do
			res:append(substitute_inner(v, mappings, context_len))
		end
		return typed_term.tuple_cons(res)
	elseif val:is_tuple_type() then
		local decls = val:unwrap_tuple_type()
		local decls = substitute_inner(decls, mappings, context_len)
		return typed_term.tuple_type(decls)
	elseif val:is_tuple_defn_type() then
		return typed_term.literal(val)
	elseif val:is_enum_value() then
		local constructor, arg = val:unwrap_enum_value()
		local arg = substitute_inner(arg, mappings, context_len)
		return typed_term.enum_cons(constructor, arg)
	elseif val:is_enum_type() then
		local decls = val:unwrap_enum_type()
		-- TODO: Handle decls properly, because it's a value.
		return typed_term.literal(val)
	elseif val:is_record_value() then
		-- TODO: How to deal with a map?
		error("Records not yet implemented")
	elseif val:is_record_type() then
		local decls = val:unwrap_record_type()
		-- TODO: Handle decls properly, because it's a value.
		error("Records not yet implemented")
	elseif val:is_record_extend_stuck() then
		-- Needs to handle the nuetral value and map of values
		error("Records not yet implemented")
	elseif val:is_object_value() then
		return typed_term.literal(val)
	elseif val:is_object_type() then
		-- local decls = val:unwrap_object_type()
		-- TODO: this needs to be evaluated properly because it contains a value
		error("Not yet implemented")
	elseif val:is_level_type() then
		return typed_term.literal(val)
	elseif val:is_number_type() then
		return typed_term.literal(val)
	elseif val:is_number() then
		return typed_term.literal(val)
	elseif val:is_level() then
		return typed_term.literal(val)
	elseif val:is_star() then
		return typed_term.literal(val)
	elseif val:is_prop() then
		return typed_term.literal(val)
	elseif val:is_neutral() then
		local nval = val:unwrap_neutral()

		if nval:is_free() then
			local free = nval:unwrap_free()
			local lookup
			if free:is_placeholder() then
				lookup = free:unwrap_placeholder()
			elseif free:is_unique() then
				lookup = free:unwrap_unique()
			elseif free:is_metavariable() then
				lookup = free:unwrap_metavariable()
			else
				error("substitute_inner NYI free with kind " .. free.kind)
			end

			local mapping = mappings[lookup]
			if mapping then
				return mapping
			end
			return typed_term.literal(val)
		end

		if nval:is_tuple_element_access_stuck() then
			local subject, index = nval:unwrap_tuple_element_access_stuck()
			local subject_term = substitute_inner(value.neutral(subject), mappings, context_len)
			return typed_term.tuple_element_access(subject_term, index)
		end

		if nval:is_prim_unwrap_stuck() then
			local boxed = nval:unwrap_prim_unwrap_stuck()
			return typed_term.prim_unwrap(substitute_inner(value.neutral(boxed), mappings, context_len))
		end

		if nval:is_prim_wrap_stuck() then
			local to_wrap = nval:unwrap_prim_wrap_stuck()
			return typed_term.prim_wrap(substitute_inner(value.neutral(to_wrap), mappings, context_len))
		end

		if nval:is_prim_unwrap_stuck() then
			local to_unwrap = nval:unwrap_prim_unwrap_stuck()
			return typed_term.prim_unwrap(substitute_inner(value.neutral(to_unwrap), mappings, context_len))
		end

		if nval:is_prim_application_stuck() then
			local fn, arg = nval:unwrap_prim_application_stuck()
			return typed_term.application(
				typed_term.literal(value.prim(fn)),
				substitute_inner(value.neutral(arg), mappings, context_len)
			)
		end

		if nval:is_prim_tuple_stuck() then
			local leading, stuck, trailing = nval:unwrap_prim_tuple_stuck()
			local elems = typed_array()
			-- leading is an array of unwrapped prims and must already be unwrapped prim values
			for _, elem in ipairs(leading) do
				local elem_value = typed_term.literal(value.prim(elem))
				elems:append(elem_value)
			end
			elems:append(substitute_inner(value.neutral(stuck), mappings, context_len))
			for _, elem in ipairs(trailing) do
				elems:append(substitute_inner(elem, mappings, context_len))
			end
			-- print("prim_tuple_stuck nval", nval)
			local result = typed_term.prim_tuple_cons(elems)
			-- print("prim_tuple_stuck result", result)
			return result
		end

		if nval:is_prim_if_stuck() then
			local subject, consequent, alternate = nval:unwrap_prim_if_stuck()
			local subject = substitute_inner(value.neutral(subject), mappings, context_len)
			local consequent = substitute_inner(consequent, mappings, context_len)
			local alternate = substitute_inner(alternate, mappings, context_len)
			return typed_term.prim_if(subject, consequent, alternate)
		end

		if nval:is_application_stuck() then
			local fn, arg = nval:unwrap_application_stuck()
			return typed_term.application(
				substitute_inner(value.neutral(fn), mappings, context_len),
				substitute_inner(arg, mappings, context_len)
			)
		end

		-- TODO: deconstruct nuetral value or something
		error("substitute_inner not implemented yet val:is_neutral - " .. tostring(nval))
	elseif val:is_prim() then
		return typed_term.literal(val)
	elseif val:is_prim_type_type() then
		return typed_term.literal(val)
	elseif val:is_prim_number_type() then
		return typed_term.literal(val)
	elseif val:is_prim_bool_type() then
		return typed_term.literal(val)
	elseif val:is_prim_string_type() then
		return typed_term.literal(val)
	elseif val:is_prim_function_type() then
		local param_type, result_type = val:unwrap_prim_function_type()
		local param_type = substitute_inner(param_type, mappings, context_len)
		local result_type = substitute_inner(result_type, mappings, context_len)
		return typed_term.prim_function_type(param_type, result_type)
	elseif val:is_prim_wrapped_type() then
		local type = val:unwrap_prim_wrapped_type()
		local type = substitute_inner(type, mappings, context_len)
		return typed_term.prim_wrapped_type(type)
	elseif val:is_prim_user_defined_type() then
		local id, family_args = val:unwrap_prim_user_defined_type()
		local res = typed_array()
		for _, v in ipairs(family_args) do
			res:append(substitute_inner(v, mappings, context_len))
		end
		return typed_term.prim_user_defined_type_cons(id, res)
	elseif val:is_prim_nil_type() then
		return typed_term.literal(val)
	elseif val:is_prim_tuple_value() then
		return typed_term.literal(val)
	elseif val:is_prim_tuple_type() then
		local decls = val:unwrap_prim_tuple_type()
		local decls = substitute_inner(decls, mappings, context_len)
		return typed_term.prim_tuple_type(decls)
	else
		error("Unhandled value kind in substitute_inner: " .. val.kind)
	end
end

--for substituting a single var at index
---@param val value
---@param index integer
---@param param_name string?
---@param typechecking_context TypecheckingContext
---@return value
local function substitute_type_variables(val, index, param_name, typechecking_context)
	param_name = param_name and "#sub-" .. param_name or "#sub-param"
	--print("value before substituting (val): (value term follows)")
	--print(val)
	local substituted = substitute_inner(val, {
		[index] = typed_term.bound_variable(1),
	}, 1)
	--print("typed term after substitution (substituted): (typed term follows)")
	--print(substituted:pretty_print(typechecking_context))
	return value.closure(param_name, substituted, runtime_context())
end

---@param val value
---@return boolean
local function is_type_of_types(val)
	return val:is_star() or val:is_prop() or val:is_prim_type_type()
end

local make_inner_context
local infer_tuple_type, infer_tuple_type_unwrapped
local make_inner_context2
local infer_tuple_type2, infer_tuple_type_unwrapped2

local check_concrete
-- indexed by kind x kind
local concrete_comparers = {}

---@alias value_comparer fun(a: value, b: value): boolean, (string|ConcreteFail)?

---@param ka string
---@param kb string
---@param comparer value_comparer
local function add_comparer(ka, kb, comparer)
	concrete_comparers[ka] = concrete_comparers[ka] or {}
	concrete_comparers[ka][kb] = comparer
end

---@class ConcreteFail

local concrete_fail_mt = {
	__tostring = function(self)
		local message = self.message
		if type(message) == "table" then
			message = table.concat(message, "")
		end
		if self.cause then
			return message .. " because:\n" .. tostring(self.cause)
		end
		return message
	end,
}
local function concrete_fail(message, cause)
	if not cause and type(message) == "string" then
		if not message then
			error "missing error message for concrete_fail"
		end
		return message
	end
	return setmetatable({
		message = message,
		cause = cause,
	}, concrete_fail_mt)
end

---@type value_comparer
local function always_fits_comparer(a, b)
	return true
end

-- prim types
for _, prim_type in ipairs({
	value.prim_number_type,
	value.prim_string_type,
	value.prim_bool_type,
	value.prim_user_defined_type({ name = "" }, value_array()),
}) do
	add_comparer(prim_type.kind, prim_type.kind, always_fits_comparer)
end

-- types of types
add_comparer(value.prim_type_type.kind, value.prim_type_type.kind, always_fits_comparer)
---@type value_comparer
local function tuple_compare(a, b)
	-- fixme lol
	local placeholder = value.neutral(neutral_value.free(free.unique({})))
	local tuple_types_a, tuple_types_b, tuple_vals, n = infer_tuple_type_unwrapped2(a, b, placeholder)
	for i = 1, n do
		local ta, tb = tuple_types_a[i], tuple_types_b[i]

		if ta ~= tb then
			if tb:is_neutral() then
				typechecker_state:queue_subtype(ta, tb, "Nuetral value in tuple_compare")
			else
				typechecker_state:queue_subtype(ta, tb, "tuple_compare")
			end
		end
	end
	return true
end
add_comparer("value.tuple_type", "value.tuple_type", tuple_compare)
add_comparer("value.prim_tuple_type", "value.prim_tuple_type", tuple_compare)
add_comparer("value.pi", "value.pi", function(a, b)
	if a == b then
		return true
	end

	local a_param_type, a_param_info, a_result_type, a_result_info = a:unwrap_pi()
	local b_param_type, b_param_info, b_result_type, b_result_info = b:unwrap_pi()

	local avis = a_param_info:unwrap_param_info():unwrap_visibility()
	local bvis = b_param_info:unwrap_param_info():unwrap_visibility()
	if avis ~= bvis and not avis:is_implicit() then
		return false, concrete_fail("pi param_info")
	end

	local apurity = a_result_info:unwrap_result_info():unwrap_result_info()
	local bpurity = b_result_info:unwrap_result_info():unwrap_result_info()
	if apurity ~= bpurity then
		return false, concrete_fail("pi result_info")
	end

	local unique_placeholder = terms.value.neutral(terms.neutral_value.free(terms.free.unique({})))
	local a_res = apply_value(a_result_type, unique_placeholder)
	local b_res = apply_value(b_result_type, unique_placeholder)
	typechecker_state:queue_constrain(a_res, FunctionRelation(UniverseOmegaRelation), b_res, "pi function results")
	typechecker_state:queue_subtype(b_param_type, a_param_type, "pi function parameters")

	return true
end)
add_comparer("value.prim_function_type", "value.prim_function_type", function(a, b)
	if a == b then
		return true
	end

	local a_param_type, a_result_type = a:unwrap_pi()
	local b_param_type, b_result_type = b:unwrap_pi()

	local unique_placeholder = terms.value.neutral(terms.neutral_value.free(terms.free.unique({})))
	local a_res = apply_value(a_result_type, unique_placeholder)
	local b_res = apply_value(b_result_type, unique_placeholder)
	typechecker_state:queue_subtype(a_param_type, b_param_type, "prim function results")
	typechecker_state:queue_constrain(b_res, FunctionRelation(UniverseOmegaRelation), a_res, "prim function parameters")
	return true
end)

for _, type_of_type in ipairs({
	value.prim_type_type,
}) do
	add_comparer(type_of_type.kind, value.star(0).kind, always_fits_comparer)
end

add_comparer(value.star(0).kind, value.star(0).kind, function(a, b)
	local alevel = a:unwrap_star()
	local blevel = b:unwrap_star()
	if alevel > blevel then
		print("star-comparer error:")
		print("a:", alevel)
		print("b:", blevel)
		return false, "a.level > b.level"
	end
	return true
end)

add_comparer("value.prim_wrapped_type", "value.prim_wrapped_type", function(a, b)
	local ua, ub = a:unwrap_prim_wrapped_type(), b:unwrap_prim_wrapped_type()
	typechecker_state:queue_subtype(ua, ub)
	--U.tag("check_concrete", { ua, ub }, check_concrete, ua, ub)
	return true
end)

add_comparer("value.singleton", "value.singleton", function(a, b)
	local a_supertype, a_value = a:unwrap_singleton()
	local b_supertype, b_value = b:unwrap_singleton()
	typechecker_state:queue_subtype(a_supertype, b_supertype, "singleton")

	if a_value == b_value then
		return true
	else
		return false, "unequal singletons"
	end
end)

-- Compares any non-metavariables, or defers any metavariable comparisons to the work queue
---@param val value
---@param use value
---@return boolean
---@return string?
function check_concrete(val, use)
	assert(val and use, "nil value or usage passed into check_concrete!")

	if val:is_neutral() and use:is_neutral() then
		if val == use then
			return true
		end
		return false, "both values are neutral, but they aren't equal: " .. tostring(val) .. " ~= " .. tostring(use)
	end

	if val:is_singleton() and not use:is_singleton() then
		local val_supertype, _ = val:unwrap_singleton()
		typechecker_state:queue_subtype(val_supertype, use, "singleton subtype")
		return true
	end

	if not concrete_comparers[val.kind] then
		error("No valid concrete type comparer found for value " .. val.kind .. ": " .. tostring(val))
	end

	local comparer = (concrete_comparers[val.kind] or {})[use.kind]
	if not comparer then
		return false,
			"no valid concerete comparer between value " .. val.kind .. " and usage " .. use.kind .. ": " .. tostring(
				val
			) .. " compared against " .. tostring(use)
	end

	return comparer(val, use)
end

---@param enum_val value
---@param closures Array
---@return Array
local function extract_tuple_elem_type_closures(enum_val, closures)
	local constructor, arg = enum_val:unwrap_enum_value()
	local elements = arg:unwrap_tuple_value()
	if constructor == terms.DeclCons.empty then
		if #elements ~= 0 then
			error "enum_value with constructor empty should have no args"
		end
		return closures
	end
	if constructor == terms.DeclCons.cons then
		if #elements ~= 2 then
			error "enum_value with constructor cons should have two args"
		end
		extract_tuple_elem_type_closures(elements[1], closures)
		if not elements[2]:is_closure() then
			error "second elem in tuple_type enum_value should be closure"
		end
		closures:append(elements[2])
		return closures
	end
	error "unknown enum constructor for value.tuple_type's enum_value, should not be reachable"
end

---@param checkable_term checkable
---@param typechecking_context TypecheckingContext
---@param goal_type value
---@return Array, typed
function check(
	checkable_term, -- constructed from checkable_term
	typechecking_context, -- todo
	goal_type
) -- must be unify with goal type (there is some way we can assign metavariables to make them equal)
	-- -> usage counts, a typed term
	if terms.checkable_term.value_check(checkable_term) ~= true then
		error("check, checkable_term: expected a checkable term")
	end
	if terms.typechecking_context_type.value_check(typechecking_context) ~= true then
		error("check, typechecking_context: expected a typechecking context")
	end
	if terms.value.value_check(goal_type) ~= true then
		print("goal_type", goal_type)
		error("check, goal_type: expected a goal type (as an alicorn value)")
	end

	if checkable_term:is_inferrable() then
		local inferrable_term = checkable_term:unwrap_inferrable()
		local inferred_type, inferred_usages, typed_term = infer(inferrable_term, typechecking_context)
		-- TODO: unify!!!!
		if inferred_type ~= goal_type then
			-- FIXME: needs context to avoid bugs where inferred and goal are the same neutral structurally
			-- but come from different context thus are different
			-- but erroneously compare equal
			typechecker_state:flow(inferred_type, typechecking_context, goal_type, typechecking_context)
		end
		return inferred_usages, typed_term
	elseif checkable_term:is_tuple_cons() then
		local elements = checkable_term:unwrap_tuple_cons()
		local usages = usage_array()
		local new_elements = typed_array()
		local decls = terms.empty

		for _, v in ipairs(elements) do
			local el_type_metavar = typechecker_state:metavariable(typechecking_context)
			local el_type = el_type_metavar:as_value()
			local el_usages, el_term = check(v, typechecking_context, el_type)

			add_arrays(usages, el_usages)
			new_elements:append(el_term)

			local el_val = evaluate(el_term, typechecking_context.runtime_context)

			decls = terms.cons(
				decls,
				value.closure(
					"#check-tuple-cons-param",
					typed_term.literal(value.singleton(el_type, el_val)),
					typechecking_context.runtime_context
				)
			)
		end

		typechecker_state:flow(
			value.tuple_type(decls),
			typechecking_context,
			goal_type,
			typechecking_context,
			"checkable_term:is_tuple_cons"
		)

		return usages, typed_term.tuple_cons(new_elements)
	elseif checkable_term:is_prim_tuple_cons() then
		local elements = checkable_term:unwrap_prim_tuple_cons()
		local usages = usage_array()
		local new_elements = typed_array()
		local decls = terms.empty

		for _, v in ipairs(elements) do
			local el_type_metavar = typechecker_state:metavariable(typechecking_context)
			local el_type = el_type_metavar:as_value()
			local el_usages, el_term = check(v, typechecking_context, el_type)

			add_arrays(usages, el_usages)
			new_elements:append(el_term)

			local el_val = evaluate(el_term, typechecking_context.runtime_context)

			decls = terms.cons(
				decls,
				value.closure(
					"#check-tuple-cons-param",
					typed_term.literal(value.singleton(el_type, el_val)),
					typechecking_context.runtime_context
				)
			)
		end

		typechecker_state:flow(
			value.prim_tuple_type(decls),
			typechecking_context,
			goal_type,
			typechecking_context,
			"checkable_term:is_prim_tuple_cons"
		)

		return usages, typed_term.prim_tuple_cons(new_elements)
	elseif checkable_term:is_lambda() then
		local param_name, body = checkable_term:unwrap_lambda()
		-- assert that goal_type is a pi type
		-- TODO open says work on other things first they will be easier
		error("nyi")
	else
		error("check: unknown kind: " .. checkable_term.kind)
	end

	error("unreachable!?")
end

---apply an alicorn function to an alicorn value
---@param f value
---@param arg value
---@return value
function apply_value(f, arg)
	if terms.value.value_check(f) ~= true then
		error("apply_value, f: expected an alicorn value")
	end
	if terms.value.value_check(arg) ~= true then
		error("apply_value, arg: expected an alicorn value")
	end

	if f:is_closure() then
		local param_name, code, capture = f:unwrap_closure()
		return U.notail(U.tag("evaluate", code, evaluate, code, capture:append(arg)))
	elseif f:is_neutral() then
		return value.neutral(neutral_value.application_stuck(f:unwrap_neutral(), arg))
	elseif f:is_prim() then
		local prim_func_impl = f:unwrap_prim()
		if prim_func_impl == nil then
			error "expected to get a function but found nil, did you forget to return the function from an intrinsic"
		end
		if arg:is_prim_tuple_value() then
			local arg_elements = arg:unwrap_prim_tuple_value()
			return value.prim_tuple_value(primitive_array(prim_func_impl(arg_elements:unpack())))
		elseif arg:is_neutral() then
			return value.neutral(neutral_value.prim_application_stuck(prim_func_impl, arg:unwrap_neutral()))
		else
			error("apply_value, is_prim, arg: expected a prim tuple argument")
		end
	else
		p(f)
		error("apply_value, f: expected a function/closure")
	end

	error("unreachable!?")
end

---@param subject value
---@param index integer
---@return value
local function index_tuple_value(subject, index)
	if terms.value.value_check(subject) ~= true then
		error("index_tuple_value, subject: expected an alicorn value")
	end

	if subject:is_tuple_value() then
		local elems = subject:unwrap_tuple_value()
		return elems[index]
	elseif subject:is_prim_tuple_value() then
		local elems = subject:unwrap_prim_tuple_value()
		return value.prim(elems[index])
	elseif subject:is_neutral() then
		local inner = subject:unwrap_neutral()
		if inner:is_prim_tuple_stuck() then
			local leading, stuck_elem, trailing = inner:unwrap_prim_tuple_stuck()
			if #leading >= index then
				return terms.value.prim(leading[index])
			elseif #leading + 1 == index then
				return terms.value.neutral(stuck_elem)
			elseif #leading + 1 + #trailing >= index then
				return trailing[index - #leading - 1]
			else
				error "tuple index out of bounds"
			end
		end
		return value.neutral(neutral_value.tuple_element_access_stuck(inner, index))
	end
	error("Should be unreachable???")
end

---@param subject_type value
---@param subject_value value
---@return value
---@return fun(i: any) : value
local function make_tuple_prefix(subject_type, subject_value)
	local decls, make_prefix
	if subject_type:is_tuple_type() then
		decls = subject_type:unwrap_tuple_type()

		if subject_value:is_tuple_value() then
			local subject_elements = subject_value:unwrap_tuple_value()
			function make_prefix(i)
				return value.tuple_value(subject_elements:copy(1, i))
			end
		elseif subject_value:is_neutral() then
			local subject_neutral = subject_value:unwrap_neutral()
			function make_prefix(i)
				local prefix_elements = value_array()
				for x = 1, i do
					prefix_elements:append(value.neutral(neutral_value.tuple_element_access_stuck(subject_neutral, x)))
				end
				return value.tuple_value(prefix_elements)
			end
		else
			error("make_tuple_prefix, is_tuple_type, subject_value: expected a tuple")
		end
	elseif subject_type:is_prim_tuple_type() then
		decls = subject_type:unwrap_prim_tuple_type()

		if subject_value:is_prim_tuple_value() then
			local subject_elements = subject_value:unwrap_prim_tuple_value()
			local subject_value_elements = value_array()
			for _, v in ipairs(subject_elements) do
				subject_value_elements:append(value.prim(v))
			end
			function make_prefix(i)
				return value.tuple_value(subject_value_elements:copy(1, i))
			end
		elseif subject_value:is_neutral() then
			-- yes, literally a copy-paste of the neutral case above
			local subject_neutral = subject_value:unwrap_neutral()
			function make_prefix(i)
				local prefix_elements = value_array()
				for x = 1, i do
					prefix_elements:append(value.neutral(neutral_value.tuple_element_access_stuck(subject_neutral, x)))
				end
				return value.tuple_value(prefix_elements)
			end
		else
			error("make_tuple_prefix, is_prim_tuple_type, subject_value: expected a primitive tuple")
		end
	else
		print(subject_type:pretty_print())
		error("make_tuple_prefix, subject_type: expected a term with a tuple type, but got " .. subject_type.kind)
	end

	return decls, make_prefix
end

-- TODO: create a typechecking context append variant that merges two
---@param decls value
---@param make_prefix fun(i: integer): value
---@return value[]
---@return integer
---@return value[]
function make_inner_context(decls, make_prefix)
	-- evaluate the type of the tuple
	local constructor, arg = decls:unwrap_enum_value()
	if constructor == terms.DeclCons.empty then
		return value_array(), 0, value_array()
	elseif constructor == terms.DeclCons.cons then
		local details = arg:unwrap_tuple_value()
		local tupletypes, n_elements, tuplevals = make_inner_context(details[1], make_prefix)
		local f = details[2]
		local element_type
		if #tupletypes == #tuplevals then
			local prefix = value.tuple_value(tuplevals)
			element_type = apply_value(f, prefix)
			if element_type:is_singleton() then
				local _, val = element_type:unwrap_singleton()
				tuplevals:append(val)
			end
		else
			local prefix = make_prefix(n_elements)
			element_type = apply_value(f, prefix)
		end
		tupletypes:append(element_type)
		return tupletypes, n_elements + 1, tuplevals
	else
		error("infer: unknown tuple type data constructor")
	end
end

---@param subject_type value
---@param subject_value value
---@return value[]
---@return integer
---@return value[]
function infer_tuple_type_unwrapped(subject_type, subject_value)
	local decls, make_prefix = make_tuple_prefix(subject_type, subject_value)
	return make_inner_context(decls, make_prefix)
end

---@param subject_type value
---@param subject_value value
---@return value[]
---@return integer
---@return value[]
function infer_tuple_type(subject_type, subject_value)
	-- define how the type of each tuple element should be evaluated
	return infer_tuple_type_unwrapped(subject_type, subject_value)
end

---@param decls_a value
---@param make_prefix_a fun(i: integer): value
---@param decls_b value
---@param make_prefix_b fun(i: integer): value
---@return value[]
---@return value[]
---@return value[]
---@return integer
function make_inner_context2(decls_a, make_prefix_a, decls_b, make_prefix_b)
	local constructor_a, arg_a = decls_a:unwrap_enum_value()
	local constructor_b, arg_b = decls_b:unwrap_enum_value()
	if constructor_a == terms.DeclCons.empty and constructor_b == terms.DeclCons.empty then
		return value_array(), value_array(), value_array(), 0
	elseif constructor_a == terms.DeclCons.empty or constructor_b == terms.DeclCons.empty then
		error("tuple decls lengths must be equal")
	elseif constructor_a == terms.DeclCons.cons and constructor_b == terms.DeclCons.cons then
		local details_a = arg_a:unwrap_tuple_value()
		local details_b = arg_b:unwrap_tuple_value()
		local tupletypes_a, tupletypes_b, tuplevals, n_elements =
			make_inner_context2(details_a[1], make_prefix_a, details_b[1], make_prefix_b)
		local f_a = details_a[2]
		local f_b = details_b[2]
		local element_type_a
		local element_type_b
		if #tupletypes_a == #tuplevals then
			local prefix = value.tuple_value(tuplevals)
			element_type_a = apply_value(f_a, prefix)
			element_type_b = apply_value(f_b, prefix)
			if element_type_a:is_singleton() then
				local _, val = element_type_a:unwrap_singleton()
				tuplevals:append(val)
			elseif element_type_b:is_singleton() then
				local _, val = element_type_b:unwrap_singleton()
				tuplevals:append(val)
			end
		else
			local prefix_a = make_prefix_a(n_elements)
			local prefix_b = make_prefix_b(n_elements)
			element_type_a = apply_value(f_a, prefix_a)
			element_type_b = apply_value(f_b, prefix_b)
		end
		tupletypes_a:append(element_type_a)
		tupletypes_b:append(element_type_b)
		return tupletypes_a, tupletypes_b, tuplevals, n_elements + 1
	else
		error("infer: unknown tuple type data constructor")
	end
end

---@param subject_type_a value
---@param subject_type_b value
---@param subject_value value
---@return value[]
---@return value[]
---@return value[]
---@return integer
function infer_tuple_type_unwrapped2(subject_type_a, subject_type_b, subject_value)
	local decls_a, make_prefix_a = make_tuple_prefix(subject_type_a, subject_value)
	local decls_b, make_prefix_b = make_tuple_prefix(subject_type_b, subject_value)
	return make_inner_context2(decls_a, make_prefix_a, decls_b, make_prefix_b)
end

---@param typ value
---@return integer
local function nearest_star_level(typ)
	if typ:is_prim_type_type() then
		return 0
	elseif typ:is_star() then
		return typ:unwrap_star()
	else
		print(typ.kind, typ)
		error "unknown sort in nearest_star, please expand or build a proper least upper bound"
	end
end

---@param inferrable_term inferrable
---@param typechecking_context TypecheckingContext
---@return value, Array, typed
function infer(
	inferrable_term, -- constructed from inferrable
	typechecking_context -- todo
)
	-- -> type of term, usage counts, a typed term,
	if terms.inferrable_term.value_check(inferrable_term) ~= true then
		error("infer, inferrable_term: expected an inferrable term")
	end
	if terms.typechecking_context_type.value_check(typechecking_context) ~= true then
		error("infer, typechecking_context: expected a typechecking context")
	end

	if inferrable_term:is_bound_variable() then
		local index = inferrable_term:unwrap_bound_variable()
		local typeof_bound = typechecking_context:get_type(index)
		local usage_counts = usage_array()
		local context_size = #typechecking_context
		for _ = 1, context_size do
			usage_counts:append(0)
		end
		usage_counts[index] = 1
		local bound = typed_term.bound_variable(index)
		return typeof_bound, usage_counts, bound
	elseif inferrable_term:is_annotated() then
		local checkable_term, inferrable_goal_type = inferrable_term:unwrap_annotated()
		local type_of_type, usages, goal_typed_term = infer(inferrable_goal_type, typechecking_context)
		local goal_type = evaluate(goal_typed_term, typechecking_context.runtime_context)
		return goal_type, check(checkable_term, typechecking_context, goal_type)
	elseif inferrable_term:is_typed() then
		return inferrable_term:unwrap_typed()
	elseif inferrable_term:is_annotated_lambda() then
		local param_name, param_annotation, body, anchor, param_visibility = inferrable_term:unwrap_annotated_lambda()
		local _, _, param_term = infer(param_annotation, typechecking_context)
		local param_type = evaluate(param_term, typechecking_context:get_runtime_context())
		local inner_context = typechecking_context:append(param_name, param_type, nil, anchor)
		local body_type, body_usages, body_term = infer(body, inner_context)

		local result_type = substitute_type_variables(body_type, #inner_context, param_name, typechecking_context)
		--print("INFER ANNOTATED LAMBDA")
		--print("result_type")
		--print(result_type:pretty_print(typechecking_context))
		local body_usages_param = body_usages[#body_usages]
		local lambda_usages = body_usages:copy(1, #body_usages - 1)
		local lambda_type =
			value.pi(param_type, value.param_info(value.visibility(param_visibility)), result_type, result_info_pure)
		local lambda_term = typed_term.lambda(param_name, body_term)
		return lambda_type, lambda_usages, lambda_term
	elseif inferrable_term:is_pi() then
		local param_type, param_info, result_type, result_info = inferrable_term:unwrap_pi()
		local param_type_type, param_type_usages, param_type_term = infer(param_type, typechecking_context)
		local param_info_usages, param_info_term = check(param_info, typechecking_context, value.param_info_type)
		local result_type_type, result_type_usages, result_type_term = infer(result_type, typechecking_context)
		local result_info_usages, result_info_term = check(result_info, typechecking_context, value.result_info_type)
		if not result_type_type:is_pi() then
			error "result type of a pi term must infer to a pi because it must be callable"
			-- TODO: switch to using a mechanism term system
		end
		local result_type_param_type, result_type_param_info, result_type_result_type, result_type_result_info =
			result_type_type:unwrap_pi()

		if not result_type_result_info:unwrap_result_info():unwrap_result_info():is_pure() then
			error "result type computation must be pure for now"
		end

		typechecker_state:flow(
			evaluate(param_type_term, typechecking_context.runtime_context),
			typechecking_context,
			result_type_param_type,
			typechecking_context,
			"inferrable pi term"
		)
		local result_type_result_type_result =
			apply_value(result_type_result_type, evaluate(param_type_term, typechecking_context.runtime_context))
		local sort = value.star(
			math.max(nearest_star_level(param_type_type), nearest_star_level(result_type_result_type_result), 0)
		)

		local term = typed_term.pi(param_type_term, param_info_term, result_type_term, result_info_term)

		local usages = usage_array()
		add_arrays(usages, param_type_usages)
		add_arrays(usages, param_info_usages)
		add_arrays(usages, result_type_usages)
		add_arrays(usages, result_info_usages)

		return sort, usages, term
	elseif inferrable_term:is_application() then
		local f, arg = inferrable_term:unwrap_application()
		local f_type, f_usages, f_term = infer(f, typechecking_context)

		if f_type:is_pi() then
			local f_param_type, f_param_info, f_result_type, f_result_info = f_type:unwrap_pi()
			while f_param_info:unwrap_param_info():unwrap_visibility():is_implicit() do
				local metavar = typechecker_state:metavariable(typechecking_context)
				local metaresult = apply_value(f_result_type, metavar:as_value())
				if not metaresult:is_pi() then
					error(
						"calling function with implicit args, result type applied on implicit args must be a function type"
					)
				end
				f_term = typed_term.application(f_term, typed_term.literal(metavar:as_value()))
				f_param_type, f_param_info, f_result_type, f_result_info = metaresult:unwrap_pi()
			end

			local arg_usages, arg_term = check(arg, typechecking_context, f_param_type)

			local application_usages = usage_array()
			add_arrays(application_usages, f_usages)
			add_arrays(application_usages, arg_usages)
			local application = typed_term.application(f_term, arg_term)

			-- check already checked for us so no check_concrete
			local arg_value = evaluate(arg_term, typechecking_context:get_runtime_context())
			local application_result_type = apply_value(f_result_type, arg_value)

			if value.value_check(application_result_type) ~= true then
				local bindings = typechecking_context:get_runtime_context().bindings
				error("application_result_type isn't a value inferring application of pi type")
			end
			return application_result_type, application_usages, application
		elseif f_type:is_prim_function_type() then
			local f_param_type, f_result_type_closure = f_type:unwrap_prim_function_type()

			local arg_usages, arg_term = check(arg, typechecking_context, f_param_type)

			local application_usages = usage_array()
			add_arrays(application_usages, f_usages)
			add_arrays(application_usages, arg_usages)
			local application = typed_term.application(f_term, arg_term)

			-- check already checked for us so no check_concrete
			local f_result_type =
				apply_value(f_result_type_closure, evaluate(arg_term, typechecking_context:get_runtime_context()))
			if value.value_check(f_result_type) ~= true then
				error("application_result_type isn't a value inferring application of prim_function_type")
			end
			return f_result_type, application_usages, application
		else
			p(f_type)
			error("infer, is_application, f_type: expected a term with a function type")
		end
	elseif inferrable_term:is_tuple_cons() then
		local elements = inferrable_term:unwrap_tuple_cons()
		-- type_data is either "empty", an empty tuple,
		-- or "cons", a tuple with the previous type_data and a function that
		-- takes all previous values and produces the type of the next element
		local type_data = terms.empty
		local usages = usage_array()
		local new_elements = typed_array()
		for _, v in ipairs(elements) do
			local el_type, el_usages, el_term = infer(v, typechecking_context)
			local el_val = evaluate(el_term, typechecking_context.runtime_context)
			type_data = terms.cons(
				type_data,
				value.singleton(
					substitute_type_variables(el_type, #typechecking_context + 1, nil, typechecking_context),
					el_val
				)
			)
			add_arrays(usages, el_usages)
			new_elements:append(el_term)
		end
		return value.tuple_type(type_data), usages, typed_term.tuple_cons(new_elements)
	elseif inferrable_term:is_prim_tuple_cons() then
		--print "inferring tuple construction"
		--print(inferrable_term:pretty_print())
		--print "environment_names"
		--for i = 1, #typechecking_context do
		--	print(i, typechecking_context:get_name(i))
		--end
		local elements = inferrable_term:unwrap_prim_tuple_cons()
		-- type_data is either "empty", an empty tuple,
		-- or "cons", a tuple with the previous type_data and a function that
		-- takes all previous values and produces the type of the next element
		-- TODO: it is a type error to put something that isn't a prim into a prim tuple
		local type_data = terms.empty
		local usages = usage_array()
		local new_elements = typed_array()
		for _, v in ipairs(elements) do
			local el_type, el_usages, el_term = infer(v, typechecking_context)
			--print "inferring element of tuple construction"
			--print(el_type:pretty_print())
			local el_val = evaluate(el_term, typechecking_context.runtime_context)
			type_data = terms.cons(
				type_data,
				value.singleton(
					substitute_type_variables(el_type, #typechecking_context + 1, nil, typechecking_context),
					el_val
				)
			)
			add_arrays(usages, el_usages)
			new_elements:append(el_term)
		end
		return value.prim_tuple_type(type_data), usages, typed_term.prim_tuple_cons(new_elements)
	elseif inferrable_term:is_tuple_elim() then
		local names, subject, body = inferrable_term:unwrap_tuple_elim()
		local subject_type, subject_usages, subject_term = infer(subject, typechecking_context)

		-- evaluating the subject is necessary for inferring the type of the body
		local subject_value = evaluate(subject_term, typechecking_context:get_runtime_context())
		local tupletypes, n_elements = infer_tuple_type(subject_type, subject_value)

		local inner_context = typechecking_context

		for i, v in ipairs(tupletypes) do
			inner_context = inner_context:append("#tuple_element_" .. i, v, index_tuple_value(subject_value, i))
		end

		-- infer the type of the body, now knowing the type of the tuple
		local body_type, body_usages, body_term = infer(body, inner_context)

		local result_usages = usage_array()
		add_arrays(result_usages, subject_usages)
		add_arrays(result_usages, body_usages)
		return body_type, result_usages, typed_term.tuple_elim(names, subject_term, n_elements, body_term)
	elseif inferrable_term:is_tuple_type() then
		local definition = inferrable_term:unwrap_tuple_type()
		local definition_type, definition_usages, definition_term = infer(definition, typechecking_context)
		if not definition_type:is_tuple_defn_type() then
			error "argument to tuple_type is not a tuple_defn"
		end
		return terms.value.star(0), definition_usages, terms.typed_term.tuple_type(definition_term)
	elseif inferrable_term:is_record_cons() then
		local fields = inferrable_term:unwrap_record_cons()
		-- type_data is either "empty", an empty tuple,
		-- or "cons", a tuple with the previous type_data and a function that
		-- takes all previous values and produces the type of the next element
		local type_data = terms.empty
		local usages = usage_array()
		local new_fields = string_typed_map()
		for k, v in pairs(fields) do
			local field_type, field_usages, field_term = infer(v, typechecking_context)
			type_data = terms.cons(
				type_data,
				value.name(k),
				substitute_type_variables(field_type, #typechecking_context + 1, nil, typechecking_context)
			)
			add_arrays(usages, field_usages)
			new_fields[k] = field_term
		end
		return value.record_type(type_data), usages, typed_term.record_cons(new_fields)
	elseif inferrable_term:is_record_elim() then
		local subject, field_names, body = inferrable_term:unwrap_record_elim()
		local subject_type, subject_usages, subject_term = infer(subject, typechecking_context)
		local ok, decls = subject_type:as_record_type()
		if not ok then
			error("infer, is_record_elim, subject_type: expected a term with a record type")
		end
		-- evaluating the subject is necessary for inferring the type of the body
		local subject_value = evaluate(subject_term, typechecking_context:get_runtime_context())

		-- define how the type of each record field should be evaluated
		local make_prefix
		if subject_value:is_record_value() then
			local subject_fields = subject_value:unwrap_record_value()
			function make_prefix(field_names)
				local prefix_fields = string_value_map()
				for _, v in ipairs(field_names) do
					prefix_fields[v] = subject_fields[v]
				end
				return value.record_value(prefix_fields)
			end
		elseif subject_value:is_neutral() then
			local subject_neutral = subject_value:unwrap_neutral()
			function make_prefix(field_names)
				local prefix_fields = string_value_map()
				for _, v in ipairs(field_names) do
					prefix_fields[v] = value.neutral(neutral_value.record_field_access_stuck(subject_neutral, v))
				end
				return value.record_value(prefix_fields)
			end
		else
			error("infer, is_record_elim, subject_value: expected a record")
		end

		-- evaluate the type of the record
		local function make_type(decls)
			local constructor, arg = decls:unwrap_enum_value()
			if constructor == terms.DeclCons.empty then
				return string_array(), string_value_map()
			elseif constructor == terms.DeclCons.cons then
				local details = arg:unwrap_tuple_value()
				local field_names, field_types = make_type(details[1])
				local name = details[2]:unwrap_name()
				local f = details[3]
				local prefix = make_prefix(field_names)
				local field_type = apply_value(f, prefix)
				field_names:append(name)
				field_types[name] = field_type
				return field_names, field_types
			else
				error("infer: unknown tuple type data constructor")
			end
		end
		local decls_field_names, decls_field_types = make_type(decls)

		-- reorder the fields into the requested order
		local inner_context = typechecking_context
		for _, v in ipairs(field_names) do
			local t = decls_field_types[v]
			if t == nil then
				error("infer: trying to access a nonexistent record field")
			end
			inner_context = inner_context:append(v, t)
		end

		-- infer the type of the body, now knowing the type of the record
		local body_type, body_usages, body_term = infer(body, inner_context)

		local result_usages = usage_array()
		add_arrays(result_usages, subject_usages)
		add_arrays(result_usages, body_usages)
		return body_type, result_usages, typed_term.record_elim(subject_term, field_names, body_term)
	elseif inferrable_term:is_enum_cons() then
		local enum_type, constructor, arg = inferrable_term:unwrap_enum_cons()
		local arg_type, arg_usages, arg_term = infer(arg, typechecking_context)
		-- TODO: check arg_type against enum_type decls
		return enum_type, arg_usages, typed_term.enum_cons(constructor, arg_term)
	elseif inferrable_term:is_enum_elim() then
		local subject, mechanism = inferrable_term:unwrap_enum_elim()
		local subject_type, subject_usages, subject_term = infer(subject, typechecking_context)
		-- local ok, decls = subject_type:as_enum_type()
		-- if not ok then
		--   error("infer, is_enum_elim, subject_type: expected a term with an enum type")
		-- end
		local mechanism_type, mechanism_usages, mechanism_term = infer(mechanism, typechecking_context)
		-- TODO: check subject decls against mechanism decls
		error("nyi")
	elseif inferrable_term:is_object_cons() then
		local methods = inferrable_term:unwrap_object_cons()
		local type_data = terms.empty
		local new_methods = string_typed_map()
		for k, v in pairs(methods) do
			local method_type, method_usages, method_term = infer(v, typechecking_context)
			type_data = terms.cons(type_data, value.name(k), method_type)
			new_methods[k] = method_term
		end
		-- TODO: usages
		return value.object_type(type_data), usage_array(), typed_term.object_cons(new_methods)
	elseif inferrable_term:is_object_elim() then
		local subject, mechanism = inferrable_term:unwrap_object_elim()
		error("nyi")
	elseif inferrable_term:is_operative_cons() then
		local operative_type, userdata = inferrable_term:unwrap_operative_cons()
		local operative_type_type, operative_type_usages, operative_type_term =
			infer(operative_type, typechecking_context)
		local operative_type_value = evaluate(operative_type_term, typechecking_context:get_runtime_context())
		local userdata_type, userdata_usages, userdata_term = infer(userdata, typechecking_context)
		local ok, op_handler, op_userdata_type = operative_type_value:as_operative_type()
		if not ok then
			error("infer, is_operative_cons, operative_type_value: expected a term with an operative type")
		end
		if userdata_type ~= op_userdata_type then
			typechecker_state:flow(userdata_type, typechecking_context, op_userdata_type, typechecking_context)
		end
		local operative_usages = usage_array()
		add_arrays(operative_usages, operative_type_usages)
		add_arrays(operative_usages, userdata_usages)
		return operative_type_value, operative_usages, typed_term.operative_cons(userdata_term)
	elseif inferrable_term:is_operative_type_cons() then
		local handler, userdata_type = inferrable_term:unwrap_operative_type_cons()
		local goal_type = value.pi(
			value.tuple_type(
				terms.cons(
					terms.cons(
						terms.cons(
							terms.cons(terms.empty, const_combinator(prim_syntax_type)),
							const_combinator(prim_environment_type)
						),
						const_combinator(prim_typed_term_type)
					),
					const_combinator(prim_goal_type)
				)
			),
			--unrestricted(tup_val(unrestricted(prim_syntax_type), unrestricted(prim_environment_type))),
			param_info_explicit,
			const_combinator(
				value.tuple_type(
					terms.cons(
						terms.cons(terms.empty, const_combinator(prim_inferrable_term_type)),
						const_combinator(prim_environment_type)
					)
				)
			),
			--unrestricted(tup_val(unrestricted(prim_inferrable_term_type), unrestricted(prim_environment_type))),
			result_info_pure
		)
		local handler_usages, handler_term = check(handler, typechecking_context, goal_type)
		local userdata_type_type, userdata_type_usages, userdata_type_term = infer(userdata_type, typechecking_context)
		local operative_type_usages = usage_array()
		add_arrays(operative_type_usages, handler_usages)
		add_arrays(operative_type_usages, userdata_type_usages)
		local handler_level = get_level(goal_type)
		local userdata_type_level = get_level(userdata_type_type)
		local operative_type_level = math.max(handler_level, userdata_type_level)
		return value.star(operative_type_level),
			operative_type_usages,
			typed_term.operative_type_cons(handler_term, userdata_type_term)
	elseif inferrable_term:is_prim_user_defined_type_cons() then
		local id, family_args = inferrable_term:unwrap_prim_user_defined_type_cons()
		local new_family_args = typed_array()
		local result_usages = usage_array()
		for _, v in ipairs(family_args) do
			local e_type, e_usages, e_term = infer(v, typechecking_context)
			-- FIXME: use e_type?
			add_arrays(result_usages, e_usages)
			new_family_args:append(e_term)
		end
		return value.prim_type_type, result_usages, typed_term.prim_user_defined_type_cons(id, new_family_args)
	elseif inferrable_term:is_prim_wrapped_type() then
		local type_inf = inferrable_term:unwrap_prim_wrapped_type()
		local content_type_type, content_type_usages, content_type_term = infer(type_inf, typechecking_context)
		if not is_type_of_types(content_type_type) then
			error "infer: type being boxed must be a type"
		end
		return value.prim_type_type, content_type_usages, typed_term.prim_wrapped_type(content_type_term)
	elseif inferrable_term:is_prim_wrap() then
		local content = inferrable_term:unwrap_prim_wrap()
		local content_type, content_usages, content_term = infer(content, typechecking_context)
		return value.prim_wrapped_type(content_type), content_usages, typed_term.prim_wrap(content_term)
	elseif inferrable_term:is_prim_unstrict_wrap() then
		local content = inferrable_term:unwrap_prim_wrap()
		local content_type, content_usages, content_term = infer(content, typechecking_context)
		return value.prim_unstrict_wrapped_type(content_type),
			content_usages,
			typed_term.prim_unstrict_wrap(content_term)
	elseif inferrable_term:is_prim_unwrap() then
		local container = inferrable_term:unwrap_prim_unwrap()
		local container_type, container_usages, container_term = infer(container, typechecking_context)
		local content_type = container_type:unwrap_prim_wrapped_type()
		return content_type, container_usages, typed_term.prim_unwrap(container_term)
	elseif inferrable_term:is_prim_unstrict_unwrap() then
		local container = inferrable_term:unwrap_prim_unwrap()
		local container_type, container_usages, container_term = infer(container, typechecking_context)
		local content_type = container_type:unwrap_prim_unstrict_wrapped_type()
		return content_type, container_usages, typed_term.prim_unstrict_unwrap(container_term)
	elseif inferrable_term:is_prim_if() then
		local subject, consequent, alternate = inferrable_term:unwrap_prim_if()
		-- for each thing in typechecking context check if it == the subject, replace with literal true
		-- same for alternate but literal false

		-- TODO: Replace this with a metavariable that both branches are put into
		local susages, sterm = check(subject, typechecking_context, terms.value.prim_bool_type)
		local ctype, cusages, cterm = infer(consequent, typechecking_context)
		local atype, ausages, aterm = infer(alternate, typechecking_context)
		local restype = typechecker_state:metavariable(typechecking_context):as_value()
		typechecker_state:flow(
			ctype,
			typechecking_context,
			restype,
			typechecking_context,
			"inferred prim if consequent"
		)
		typechecker_state:flow(atype, typechecking_context, restype, typechecking_context, "inferred prim if alternate")

		local result_usages = usage_array()
		add_arrays(result_usages, susages)
		-- FIXME: max of cusages and ausages rather than adding?
		add_arrays(result_usages, cusages)
		add_arrays(result_usages, ausages)
		return restype, result_usages, typed_term.prim_if(sterm, cterm, aterm)
	elseif inferrable_term:is_let() then
		-- print(inferrable_term:pretty_print())
		local name, expr, body = inferrable_term:unwrap_let()
		local exprtype, exprusages, exprterm = infer(expr, typechecking_context)
		typechecking_context =
			typechecking_context:append(name, exprtype, evaluate(exprterm, typechecking_context.runtime_context))
		local bodytype, bodyusages, bodyterm = infer(body, typechecking_context)

		local result_usages = usage_array()
		-- NYI usages are fucky, should remove ones not used in body
		add_arrays(result_usages, exprusages)
		add_arrays(result_usages, bodyusages)
		return bodytype, result_usages, terms.typed_term.let(name, exprterm, bodyterm)
	elseif inferrable_term:is_prim_intrinsic() then
		local source, type, anchor = inferrable_term:unwrap_prim_intrinsic()
		local source_usages, source_term = check(source, typechecking_context, value.prim_string_type)
		local type_type, type_usages, type_term = infer(type, typechecking_context) --check(type, typechecking_context, value.qtype_type(0))

		--print("prim intrinsic is inferring: (inferrable term follows)")
		--print(type:pretty_print(typechecking_context))
		--print("lowers to: (typed term follows)")
		--print(type_term:pretty_print(typechecking_context))
		--error "weird type"
		-- FIXME: type_type, source_type are ignored, need checked?
		local type_val = evaluate(type_term, typechecking_context.runtime_context)
		return type_val, source_usages, typed_term.prim_intrinsic(source_term, anchor)
	elseif inferrable_term:is_level_max() then
		local level_a, level_b = inferrable_term:unwrap_level_max()
		local arg_type_a, arg_usages_a, arg_term_a = infer(level_a, typechecking_context)
		local arg_type_b, arg_usages_b, arg_term_b = infer(level_b, typechecking_context)
		return value.level_type, usage_array(), typed_term.level_max(arg_term_a, arg_term_b)
	elseif inferrable_term:is_level_suc() then
		local previous_level = inferrable_term:unwrap_level_suc()
		local arg_type, arg_usages, arg_term = infer(previous_level, typechecking_context)
		return value.level_type, usage_array(), typed_term.level_suc(arg_term)
	elseif inferrable_term:is_level0() then
		return value.level_type, usage_array(), typed_term.level0
	elseif inferrable_term:is_prim_function_type() then
		local args, returns = inferrable_term:unwrap_prim_function_type()
		local arg_type, arg_usages, arg_term = infer(args, typechecking_context)
		local return_type, return_usages, return_term = infer(returns, typechecking_context)
		local res_usages = usage_array()
		add_arrays(res_usages, arg_usages)
		add_arrays(res_usages, return_usages)
		return value.prim_type_type, res_usages, typed_term.prim_function_type(arg_term, return_term)
	elseif inferrable_term:is_prim_tuple_type() then
		local decls = inferrable_term:unwrap_prim_tuple_type()
		local decl_type, decl_usages, decl_term = infer(decls, typechecking_context)
		if not decl_type:is_tuple_defn_type() then
			error "must be a tuple defn"
		end
		return value.star(0), decl_usages, typed_term.prim_tuple_type(decl_term)
	else
		error("infer: unknown kind: " .. inferrable_term.kind)
	end

	error("unreachable!?")
end

---Replace stuck sections in a value with a more concrete form, possibly causing cascading evaluation
---@param base value
---@param original value
---@param replacement value
local function substitute_value(base, original, replacement)
	if base == original then
		return replacement
	end
	if base:is_pi() then
		local param_type, param_info, result_type, result_info = base:unwrap_pi()
	end
end

local intrinsic_memo = setmetatable({}, { __mode = "v" })

---evaluate a typed term in a contextual
---@param typed_term typed
---@param runtime_context RuntimeContext
---@return value
function evaluate(typed_term, runtime_context)
	-- -> an alicorn value
	-- TODO: typecheck typed_term and runtime_context?
	if terms.typed_term.value_check(typed_term) ~= true then
		error("evaluate, typed_term: expected a typed term")
	end
	if terms.runtime_context_type.value_check(runtime_context) ~= true then
		error("evaluate, runtime_context: expected a runtime context")
	end

	if typed_term:is_bound_variable() then
		local rc_val = runtime_context:get(typed_term:unwrap_bound_variable())
		if rc_val == nil then
			p(typed_term)
			error("runtime_context:get() for bound_variable returned nil")
		end
		return rc_val
	elseif typed_term:is_literal() then
		return typed_term:unwrap_literal()
	elseif typed_term:is_lambda() then
		local param_name, body = typed_term:unwrap_lambda()
		return value.closure(param_name, body, runtime_context)
	elseif typed_term:is_pi() then
		local param_type, param_info, result_type, result_info = typed_term:unwrap_pi()
		local param_type_value = U.tag("evaluate", param_type, evaluate, param_type, runtime_context)
		local param_info_value = U.tag("evaluate", param_info, evaluate, param_info, runtime_context)
		local result_type_value = U.tag("evaluate", result_type, evaluate, result_type, runtime_context)
		local result_info_value = U.tag("evaluate", result_info, evaluate, result_info, runtime_context)
		return value.pi(param_type_value, param_info_value, result_type_value, result_info_value)
	elseif typed_term:is_application() then
		local f, arg = typed_term:unwrap_application()
		local f_value = U.tag("evaluate", f, evaluate, f, runtime_context)
		local arg_value = U.tag("evaluate", arg, evaluate, arg, runtime_context)
		return U.notail(apply_value(f_value, arg_value))
	elseif typed_term:is_tuple_cons() then
		local elements = typed_term:unwrap_tuple_cons()
		local new_elements = value_array()
		for _, v in ipairs(elements) do
			new_elements:append(U.tag("evaluate", v, evaluate, v, runtime_context))
		end
		return value.tuple_value(new_elements)
	elseif typed_term:is_prim_tuple_cons() then
		local elements = typed_term:unwrap_prim_tuple_cons()
		local new_elements = primitive_array()
		local stuck = false
		local stuck_element
		local trailing_values
		for i, v in ipairs(elements) do
			local element_value = U.tag("evaluate", v, evaluate, v, runtime_context)
			if element_value == nil then
				p("wtf", v.kind)
			end
			if stuck then
				trailing_values:append(element_value)
			elseif element_value:is_prim() then
				new_elements:append(element_value:unwrap_prim())
			elseif element_value:is_neutral() then
				stuck = true
				stuck_element = element_value:unwrap_neutral()
				trailing_values = value_array()
			else
				print("term that fails", typed_term)
				print("which element", i)
				print("element_value", element_value)
				error("evaluate, is_prim_tuple_cons, element_value: expected a primitive value")
			end
		end
		if stuck then
			return value.neutral(neutral_value.prim_tuple_stuck(new_elements, stuck_element, trailing_values))
		else
			return value.prim_tuple_value(new_elements)
		end
	elseif typed_term:is_tuple_elim() then
		local names, subject, length, body = typed_term:unwrap_tuple_elim()
		local subject_value = U.tag("evaluate", subject, evaluate, subject, runtime_context)
		local inner_context = runtime_context
		if subject_value:is_tuple_value() then
			local subject_elements = subject_value:unwrap_tuple_value()
			if #subject_elements ~= length then
				print("tuple has only", #subject_elements, "elements but expected", length)
				print("tuple being eliminated", subject_value)
				error("evaluate: mismatch in tuple length from typechecking and evaluation")
			end
			for i = 1, length do
				inner_context = inner_context:append(subject_elements[i])
			end
		elseif subject_value:is_prim_tuple_value() then
			local subject_elements = subject_value:unwrap_prim_tuple_value()
			local real_length = #subject_elements
			if real_length ~= length then
				print("evaluating typed tuple_elim error")
				print("got, expected:")
				print(#subject_elements, length)
				print("names:")
				print(names:pretty_print())
				print("subject:")
				print(subject:pretty_print(runtime_context))
				print("subject value:")
				--print(subject_value:pretty_print(runtime_context))
				print("<redacted>")
				print("body:")
				print(body:pretty_print(runtime_context))
				print("error commented out to allow for variable-length prim tuples via the prim-unit hack")
				print("if you're having issues check this!!!")
				--error("evaluate: mismatch in tuple length from typechecking and evaluation")
			end
			for i = 1, real_length do
				inner_context = inner_context:append(value.prim(subject_elements[i]))
			end
			for _ = real_length + 1, length do
				inner_context = inner_context:append(value.prim(nil))
			end
		elseif subject_value:is_neutral() then
			for i = 1, length do
				inner_context = inner_context:append(index_tuple_value(subject_value, i))
			end
		else
			p(subject_value)
			error("evaluate, is_tuple_elim, subject_value: expected a tuple")
		end
		return U.tag("evaluate", body, evaluate, body, inner_context)
	elseif typed_term:is_tuple_element_access() then
		local tuple_term, index = typed_term:unwrap_tuple_element_access()
		--print("tuple_element_access tuple_term: (typed term follows)")
		--print(tuple_term:pretty_print(runtime_context))
		local tuple = U.tag("evaluate", tuple_term, evaluate, tuple_term, runtime_context)
		--print("tuple_element_access tuple: (value term follows)")
		--print(tuple)
		return index_tuple_value(tuple, index)
	elseif typed_term:is_tuple_type() then
		local definition_term = typed_term:unwrap_tuple_type()
		local definition = U.tag("evaluate", definition_term, evaluate, definition_term, runtime_context)
		return terms.value.tuple_type(definition)
	elseif typed_term:is_record_cons() then
		local fields = typed_term:unwrap_record_cons()
		local new_fields = string_value_map()
		for k, v in pairs(fields) do
			new_fields[k] = U.tag("evaluate", v, evaluate, v, runtime_context)
		end
		return value.record_value(new_fields)
	elseif typed_term:is_record_elim() then
		local subject, field_names, body = typed_term:unwrap_record_elim()
		local subject_value = U.tag("evaluate", subject, evaluate, subject, runtime_context)
		local inner_context = runtime_context
		if subject_value:is_record_value() then
			local subject_fields = subject_value:unwrap_record_value()
			for _, v in ipairs(field_names) do
				inner_context = inner_context:append(subject_fields[v])
			end
		elseif subject_value:is_neutral() then
			local subject_neutral = subject_value:unwrap_neutral()
			for _, v in ipairs(field_names) do
				inner_context =
					inner_context:append(value.neutral(neutral_value.record_field_access_stuck(subject_neutral, v)))
			end
		else
			error("evaluate, is_record_elim, subject_value: expected a record")
		end
		return U.tag("evaluate", body, evaluate, body, inner_context)
	elseif typed_term:is_enum_cons() then
		local constructor, arg = typed_term:unwrap_enum_cons()
		local arg_value = U.tag("evaluate", arg, evaluate, arg, runtime_context)
		return value.enum_value(constructor, arg_value)
	elseif typed_term:is_enum_elim() then
		local subject, mechanism = typed_term:unwrap_enum_elim()
		local subject_value = U.tag("evaluate", subject, evaluate, subject, runtime_context)
		local mechanism_value = U.tag("evaluate", mechanism, evaluate, mechanism, runtime_context)
		if subject_value:is_enum_value() then
			if mechanism_value:is_object_value() then
				local constructor, arg = subject_value:unwrap_enum_value()
				local methods, capture = mechanism_value:unwrap_object_value()
				local this_method = value.closure("#ENUM_PARAM", methods[constructor], capture)
				return apply_value(this_method, arg)
			elseif mechanism_value:is_neutral() then
				-- objects and enums are categorical duals
				local mechanism_neutral = mechanism_value:unwrap_neutral()
				return value.neutral(neutral_value.object_elim_stuck(subject_value, mechanism_neutral))
			else
				error("evaluate, is_enum_elim, is_enum_value, mechanism_value: expected an object")
			end
		elseif subject_value:is_neutral() then
			local subject_neutral = subject_value:unwrap_neutral()
			return value.neutral(neutral_value.enum_elim_stuck(mechanism_value, subject_neutral))
		else
			error("evaluate, is_enum_elim, subject_value: expected an enum")
		end
	elseif typed_term:is_object_cons() then
		return value.object_value(typed_term:unwrap_object_cons(), runtime_context)
	elseif typed_term:is_object_elim() then
		local subject, mechanism = typed_term:unwrap_object_elim()
		local subject_value = evaluate(subject, runtime_context)
		local mechanism_value = evaluate(mechanism, runtime_context)
		if subject_value:is_object_value() then
			if mechanism_value:is_enum_value() then
				local methods, capture = subject_value:unwrap_object_value()
				local constructor, arg = mechanism_value:unwrap_enum_value()
				local this_method = value.closure("#OBJECT_PARAM", methods[constructor], capture)
				return apply_value(this_method, arg)
			elseif mechanism_value:is_neutral() then
				-- objects and enums are categorical duals
				local mechanism_neutral = mechanism_value:unwrap_neutral()
				return value.neutral(neutral_value.enum_elim_stuck(subject_value, mechanism_neutral))
			else
				error("evaluate, is_object_elim, is_object_value, mechanism_value: expected an enum")
			end
		elseif subject_value:is_neutral() then
			local subject_neutral = subject_value:unwrap_neutral()
			return value.neutral(neutral_value.object_elim_stuck(mechanism_value, subject_neutral))
		else
			error("evaluate, is_object_elim, subject_value: expected an object")
		end
	elseif typed_term:is_operative_cons() then
		local userdata = typed_term:unwrap_operative_cons()
		local userdata_value = evaluate(userdata, runtime_context)
		return value.operative_value(userdata_value)
	elseif typed_term:is_operative_type_cons() then
		local handler, userdata_type = typed_term:unwrap_operative_type_cons()
		local handler_value = evaluate(handler, runtime_context)
		local userdata_type_value = evaluate(userdata_type, runtime_context)
		return value.operative_type(handler_value, userdata_type_value)
	elseif typed_term:is_prim_user_defined_type_cons() then
		local id, family_args = typed_term:unwrap_prim_user_defined_type_cons()
		local new_family_args = value_array()
		for _, v in ipairs(family_args) do
			new_family_args:append(evaluate(v, runtime_context))
		end
		return value.prim_user_defined_type(id, new_family_args)
	elseif typed_term:is_prim_wrapped_type() then
		local type_term = typed_term:unwrap_prim_wrapped_type()
		local type_value = evaluate(type_term, runtime_context)
		return value.prim_wrapped_type(type_value)
	elseif typed_term:is_prim_unstrict_wrapped_type() then
		local type_term = typed_term:unwrap_prim_unstrict_wrapped_type()
		local type_value = evaluate(type_term, runtime_context)
		return value.prim_wrapped_type(type_value)
	elseif typed_term:is_prim_wrap() then
		local content = typed_term:unwrap_prim_wrap()
		local content_val = evaluate(content, runtime_context)
		if content_val:is_neutral() then
			local nval = content_val:unwrap_neutral()
			return value.neutral(neutral_value.prim_wrap_stuck(nval))
		end
		return value.prim(content_val)
	elseif typed_term:is_prim_unstrict_wrap() then
		local content = typed_term:unwrap_prim_unstrict_wrap()
		local content_val = evaluate(content, runtime_context)
		return value.prim(content_val)
	elseif typed_term:is_prim_unwrap() then
		local unwrapped = typed_term:unwrap_prim_unwrap()
		local unwrap_val = evaluate(unwrapped, runtime_context)
		if not unwrap_val.as_prim then
			print("unwrapped", unwrapped, unwrap_val)
			error "evaluate, is_prim_unwrap: missing as_prim on unwrapped prim_unwrap"
		end
		if unwrap_val:is_prim() then
			return unwrap_val:unwrap_prim()
		elseif unwrap_val:is_neutral() then
			local nval = unwrap_val:unwrap_neutral()
			if nval:is_prim_wrap_stuck() then
				return value.neutral(nval:unwrap_prim_wrap_stuck())
			else
				return value.neutral(neutral_value.prim_unwrap_stuck(nval))
			end
		else
			print("unrecognized value in unbox", unwrap_val)
			error "invalid value in unbox, must be prim or neutral"
		end
	elseif typed_term:is_prim_unstrict_unwrap() then
		local unwrapped = typed_term:unwrap_prim_unstrict_unwrap()
		local unwrap_val = evaluate(unwrapped, runtime_context)
		if not unwrap_val.as_prim then
			print("unwrapped", unwrapped, unwrap_val)
			error "evaluate, is_prim_unwrap: missing as_prim on unwrapped prim_unwrap"
		end
		if unwrap_val:is_prim() then
			return unwrap_val:unwrap_prim()
		elseif unwrap_val:is_neutral() then
			local nval = unwrap_val:unwrap_neutral()
			return value.neutral(neutral_value.prim_unwrap_stuck(nval))
		else
			print("unrecognized value in unbox", unwrap_val)
			error "invalid value in unbox, must be prim or neutral"
		end
	elseif typed_term:is_prim_if() then
		local subject, consequent, alternate = typed_term:unwrap_prim_if()
		local sval = evaluate(subject, runtime_context)
		if sval:is_prim() then
			local sbool = sval:unwrap_prim()
			if type(sbool) ~= "boolean" then
				error("subject of prim_if must be a primitive bool")
			end
			if sbool then
				return evaluate(consequent, runtime_context)
			else
				return evaluate(alternate, runtime_context)
			end
		elseif sval:is_neutral() then
			local sval_neutral = sval:unwrap_neutral()
			local inner_context_c, inner_context_a = runtime_context, runtime_context
			local ok, index = subject:as_bound_variable()
			if ok then
				inner_context_c = inner_context_c:set(index, value.prim(true))
				inner_context_a = inner_context_a:set(index, value.prim(false))
			end
			local cval = evaluate(consequent, inner_context_c)
			local aval = evaluate(alternate, inner_context_a)
			return value.neutral(neutral_value.prim_if_stuck(sval_neutral, cval, aval))
		else
			error("subject of prim_if must be prim or neutral")
		end
	elseif typed_term:is_let() then
		local name, expr, body = typed_term:unwrap_let()
		local expr_value = evaluate(expr, runtime_context)
		return evaluate(body, runtime_context:append(expr_value))
	elseif typed_term:is_prim_intrinsic() then
		local source, anchor = typed_term:unwrap_prim_intrinsic()
		local source_val = evaluate(source, runtime_context)
		if source_val:is_prim() then
			local source_str = source_val:unwrap_prim()
			if intrinsic_memo[source_str] then
				return value.prim(intrinsic_memo[source_str])
			end
			local load_env = {}
			for k, v in pairs(_G) do
				load_env[k] = v
			end
			for k, v in pairs(internals_interface) do
				load_env[k] = v
			end
			local require_generator = require "require"
			load_env.require = require_generator(anchor.sourceid)
			local res = assert(load(source_str, "prim_intrinsic", "t", load_env))()
			intrinsic_memo[source_str] = res
			return value.prim(res)
		elseif source_val:is_neutral() then
			local source_neutral = source_val:unwrap_neutral()
			return value.neutral(neutral_value.prim_intrinsic_stuck(source_neutral, anchor))
		else
			error "Tried to load an intrinsic with something that isn't a string"
		end
	elseif typed_term:is_prim_function_type() then
		local args, returns = typed_term:unwrap_prim_function_type()
		local args_val = evaluate(args, runtime_context)
		local returns_val = evaluate(returns, runtime_context)
		return value.prim_function_type(args_val, returns_val)
	elseif typed_term:is_level0() then
		return value.level(0)
	elseif typed_term:is_level_suc() then
		local previous_level = typed_term:unwrap_level_suc()
		local previous_level_value = evaluate(previous_level, runtime_context)
		local ok, level = previous_level_value:as_level()
		if not ok then
			p(previous_level_value)
			error "wrong type for previous_level"
		end
		if level > OMEGA then
			error("NYI: level too high for typed_level_suc" .. tostring(level))
		end
		return value.level(level + 1)
	elseif typed_term:is_level_max() then
		local level_a, level_b = typed_term:unwrap_level_max()
		local level_a_value = evaluate(level_a, runtime_context)
		local level_b_value = evaluate(level_b, runtime_context)
		local oka, level_a_level = level_a_value:as_level()
		local okb, level_b_level = level_b_value:as_level()
		if not oka or not okb then
			error "wrong type for level_a or level_b"
		end
		return value.level(math.max(level_a_level, level_b_level))
	elseif typed_term:is_level_type() then
		return value.level_type
	elseif typed_term:is_star() then
		local level = typed_term:unwrap_star()
		return value.star(level)
	elseif typed_term:is_prop() then
		local level = typed_term:unwrap_prop()
		return value.prop(level)
	elseif typed_term:is_prim_tuple_type() then
		local decl = typed_term:unwrap_prim_tuple_type()
		local decl_val = evaluate(decl, runtime_context)
		return value.prim_tuple_type(decl_val)
	else
		error("evaluate: unknown kind: " .. typed_term.kind)
	end

	error("unreachable!?")
end

---@class SubtypeRelation
---@field Rel value -- : (a:T,b:T) -> Prop__
---@field refl value -- : (a:T) -> Rel(a,a)
---@field antisym value -- : (a:T, B:T, Rel(a,b), Rel(b,a)) -> a == b
---@field constrain value -- : (Node(T), Node(T)) -> [TCState] ()
local SubtypeRelation = {}

---@type SubtypeRelation
local UniverseOmegaRelation = {
	Rel = luatovalue(function(a, b) end, name_array("a", "b")),
	refl = luatovalue(function(a) end, name_array("a")),
	antisym = luatovalue(function(a, b, r1, r2) end, name_array("a", "b", "r1", "r2")),
	constrain = luatovalue(function(val, use)
		local ok, err = U.tag("check_concrete", { val, use }, check_concrete, val, use)
		if not ok then
			error(err)
		end
	end, name_array("val", "use")),
}

---@class OrderedSet
---@field set { [any]: integer }
---@field array any[]
local OrderedSet = {}
local ordered_set_mt

---@param t any
---@return boolean
function OrderedSet:insert(t)
	if self.set[t] ~= nil then
		return false
	end
	self.set[t] = #self.array + 1
	U.append(self.array, t)
	return true
end

---@param t any
---@return boolean
function OrderedSet:insert_aux(t, ...)
	if self.set[t] ~= nil then
		return false
	end
	self.set[t] = #self.array + 1
	U.append(self.array, { t, ... })
	return true
end

---@return OrderedSet
function OrderedSet:shadow()
	return setmetatable({ set = U.shadowtable(self.set), array = U.shadowarray(self.array) }, ordered_set_mt)
end

ordered_set_mt = { __index = OrderedSet }

---@return OrderedSet
local function ordered_set()
	return setmetatable({ set = {}, array = {} }, ordered_set_mt)
end

---@class TraitRegistry
---@field traits { [string]: Trait }
local TraitRegistry = {}
local trait_registry_mt

function TraitRegistry:shadow()
	return setmetatable({ traits = U.shadowtable(self.traits) }, trait_registry_mt)
end

function TraitRegistry:commit()
	U.commit(self.traits)
end

trait_registry_mt = { __index = TraitRegistry }

local function trait_registry()
	return setmetatable({ traits = {} }, trait_registry_mt)
end
---@class TypeCheckerState
---@field pending ReachabilityQueue
---@field graph Reachability
---@field values [value, TypeCheckerTag, TypecheckingContext|nil][]
---@field valcheck { [value]: integer }
---@field usecheck { [value]: integer }
---@field trait_registry TraitRegistry
local TypeCheckerState = {}

---@class Reachability
---@field upsets OrderedSet[]
---@field downsets OrderedSet[]
---@field leftcallupsets OrderedSet[]
---@field leftcalldownsets OrderedSet[]
---@field rightcallupsets OrderedSet[]
---@field rightcalldownsets OrderedSet[]
local Reachability = {}
local reachability_mt

---@return integer
function Reachability:add_node()
	local prevupsets = U.dumptable(self.upsets)

	local i = #self.upsets + 1 -- Account for lua tables starting at 1
	U.append(self.upsets, ordered_set())
	U.append(self.downsets, ordered_set())
	U.append(self.leftcallupsets, ordered_set())
	U.append(self.leftcalldownsets, ordered_set())
	U.append(self.rightcallupsets, ordered_set())
	U.append(self.rightcalldownsets, ordered_set())
	assert(#self.upsets == #self.downsets, "upsets must equal downsets!")
	assert(
		#self.upsets == i,
		"i does not equal upsets?! "
			.. tostring(i)
			.. " != "
			.. tostring(#self.upsets)
			.. " ... \n"
			.. tostring(prevupsets)
			.. " ... \n"
			.. tostring(U.dumptable(self.upsets))
	)
	return i
end

---This shadowing works a bit differently because it overrides setinsert to be shadow-aware
---@return Reachability
function Reachability:shadow()
	return setmetatable({
		---@param set OrderedSet[]
		---@param k integer
		---@param v integer
		---@return boolean
		setinsert = function(set, k, v)
			if rawget(set, k) == nil then
				set[k] = set[k]:shadow()
			end
			assert(rawget(set, k) ~= nil, "failed to shadow set???")
			return set[k]:insert(v)
		end,
		---@param set OrderedSet[]
		---@param k integer
		---@param v integer
		---@param ... any
		---@return boolean
		setinsert_aux = function(set, k, v, ...)
			if rawget(set, k) == nil then
				set[k] = set[k]:shadow()
			end
			assert(rawget(set, k) ~= nil, "failed to shadow set???")
			return set[k]:insert_aux(v, ...)
		end,
		downsets = U.shadowarray(self.downsets),
		upsets = U.shadowarray(self.upsets),
		leftcalldownsets = U.shadowarray(self.leftcalldownsets),
		leftcallupsets = U.shadowarray(self.leftcallupsets),
		rightcalldownsets = U.shadowarray(self.rightcalldownsets),
		rightcallupsets = U.shadowarray(self.rightcallupsets),
	}, reachability_mt)
end

function Reachability:commit()
	U.commit(self.downsets)
	U.commit(self.upsets)
	U.commit(self.leftcalldownsets)
	U.commit(self.leftcallupsets)
	U.commit(self.rightcalldownsets)
	U.commit(self.rightcallupsets)
end

---@param set OrderedSet[]
---@param k integer
---@param v integer
---@return boolean
function Reachability.setinsert(set, k, v)
	return set[k]:insert(v)
end

---@param set OrderedSet[]
---@param k integer
---@param v integer
---@param ... any
---@return boolean
function Reachability.setinsert_aux(set, k, v, ...)
	return set[k]:insert_aux(v, ...)
end

---@class (exact) EdgeNotifConstrain
---@field kind string
---@field left integer
---@field right integer
---@field rel SubtypeRelation
---@field cause any
local EdgeNotif_Constrain = {}
local EdgeNotif_Constrain_mt = { __index = EdgeNotif_Constrain }

---@class (exact) EdgeNotifCallLeft
---@field kind string
---@field arg value
---@field left integer
---@field right integer
---@field rel SubtypeRelation
---@field cause any
local EdgeNotif_CallLeft = {}
local EdgeNotif_CallLeft_mt = { __index = EdgeNotif_CallLeft }

---@class (exact) EdgeNotifCallRight
---@field kind string
---@field left integer
---@field right integer
---@field rel SubtypeRelation
---@field arg value
---@field cause any
local EdgeNotif_CallRight = {}
local EdgeNotif_CallRight_mt = { __index = EdgeNotif_CallRight }

local EdgeNotif = {
	---@param left integer
	---@param rel SubtypeRelation
	---@param right integer
	---@param cause any
	---@return EdgeNotifConstrain
	Constrain = function(left, rel, right, cause)
		return { kind = "constrain", left = left, rel = rel, right = right, cause = cause }
	end,
	---@param left integer
	---@param argument value
	---@param rel SubtypeRelation
	---@param right integer
	---@param cause any
	---@return EdgeNotifCallLeft
	CallLeft = function(left, argument, rel, right, cause)
		return { kind = "call_left", left = left, arg = argument, rel = rel, right = right, cause = cause }
	end,
	---@param left integer
	---@param rel SubtypeRelation
	---@param right integer
	---@param argument value
	---@param cause any
	---@return EdgeNotifCallRight
	CallRight = function(left, rel, right, argument, cause)
		return { kind = "call_right", left = left, rel = rel, right = right, arg = argument, cause = cause }
	end,
}

---@alias EdgeNotif EdgeNotifConstrain | EdgeNotifCallRight | EdgeNotifCallLeft
---@alias ReachabilityQueue [EdgeNotif]

function Reachability:constrain_transitivity(left, right, queue, rel, cause)
	for _, l2 in ipairs(self.upsets[left].array) do
		if l2[2] ~= rel then
			error("Relations do not match! " .. tostring(l2[2]) .. " is not " .. tostring(rel))
		end
		U.append(queue, EdgeNotif.Constrain(l2[1], rel, right, cause))
	end
	for _, r2 in ipairs(self.downsets[right].array) do
		if r2[2] ~= rel then
			error("Relations do not match! " .. tostring(r2[2]) .. " is not " .. tostring(rel))
		end
		U.append(queue, EdgeNotif.Constrain(left, rel, r2[1], cause))
	end
end

---@param left integer
---@param right integer
---@param rel SubtypeRelation
---@return boolean
function Reachability:add_constrain_edge(left, right, rel)
	assert(type(left) == "number", "left isn't an integer!")
	assert(type(right) == "number", "right isn't an integer!")

	assert(self.downsets[left], "Can't find " .. tostring(left))
	if self.setinsert_aux(self.downsets, left, right, rel) then
		assert(self.downsets[right], "Can't find " .. tostring(right))
		self.setinsert_aux(self.upsets, right, left, rel)

		return true
	end

	return false
end

---@param left integer
---@param arg value
---@param rel SubtypeRelation
---@param right integer
---@return boolean
function Reachability:add_call_left_edge(left, arg, rel, right)
	assert(type(left) == "number", "left isn't an integer!")
	assert(type(right) == "number", "right isn't an integer!")

	assert(self.leftcalldownsets[left], "Can't find " .. tostring(left))
	if self.setinsert_aux(self.leftcalldownsets, left, right, arg, rel) then
		assert(self.leftcalldownsets[right], "Can't find " .. tostring(right))
		self.setinsert_aux(self.leftcallupsets, right, left, arg, rel)

		return true
	end

	return false
end

---@param left integer
---@param rel SubtypeRelation
---@param right integer
---@param arg value
---@return boolean
function Reachability:add_call_right_edge(left, rel, right, arg)
	assert(type(left) == "number", "left isn't an integer!")
	assert(type(right) == "number", "right isn't an integer!")

	assert(self.rightcalldownsets[left], "Can't find " .. tostring(left))
	if self.setinsert_aux(self.rightcalldownsets, left, right, arg, rel) then
		assert(self.rightcalldownsets[right], "Can't find " .. tostring(right))
		self.setinsert_aux(self.rightcallupsets, right, left, arg, rel)

		return true
	end

	return false
end

function Reachability:add_call_edge(left, right, queue, rel, cause)
	assert(type(left) == "number", "left isn't an integer!")
	assert(type(right) == "number", "right isn't an integer!")
end

reachability_mt = { __index = Reachability }

---@return Reachability
local function reachability()
	return setmetatable({
		downsets = {},
		upsets = {},
		leftcalldownsets = {},
		leftcallupsets = {},
		rightcalldownsets = {},
		rightcallupsets = {},
	}, reachability_mt)
end

---@class TypeCheckerTag
local TypeCheckerTag = {
	VALUE = {},
	USAGE = {},
	VAR = {},
}
---@param val value
---@param use value
---@param cause any
function TypeCheckerState:queue_subtype(val, use, cause)
	local l = U.tag("check_value", { val, use }, self.check_value, self, val, TypeCheckerTag.VALUE, nil)
	local r = U.tag("check_value", { val, use }, self.check_value, self, use, TypeCheckerTag.USAGE, nil)
	assert(type(l) == "number", "l isn't number, instead found " .. tostring(l))
	assert(type(r) == "number", "r isn't number, instead found " .. tostring(r))
	U.append(self.pending, EdgeNotif.Constrain(l, UniverseOmegaRelation, r, cause))
end

---@param val value
---@param rel SubtypeRelation
---@param use value
---@param cause any
function TypeCheckerState:queue_constrain(val, rel, use, cause)
	local l = U.tag("check_value", { val, use }, self.check_value, self, val, TypeCheckerTag.VALUE, nil)
	local r = U.tag("check_value", { val, use }, self.check_value, self, use, TypeCheckerTag.USAGE, nil)
	assert(type(l) == "number", "l isn't number, instead found " .. tostring(l))
	assert(type(r) == "number", "r isn't number, instead found " .. tostring(r))
	U.append(self.pending, EdgeNotif.Constrain(l, rel, r, cause))
end

---@param v value
---@param tag TypeCheckerTag
---@param context TypecheckingContext|nil
---@return integer
function TypeCheckerState:check_value(v, tag, context)
	assert(v, "nil passed into check_value!")

	if v:is_neutral() and v:unwrap_neutral():is_free() and v:unwrap_neutral():unwrap_free():is_metavariable() then
		local mv = v:unwrap_neutral():unwrap_free():unwrap_metavariable()
		if mv.value == 339 or mv.usage == 339 then
			--error("339!!!!!")
		end
		if tag == TypeCheckerTag.VALUE then
			assert(mv.value ~= nil)
			return mv.value
		else
			assert(mv.usage ~= nil)
			return mv.usage
		end
	end

	--if v:is_neutral() then
	--error("Don't know how to process nuetral value! " .. tostring(v))
	--end

	local checker = self.valcheck
	if tag == TypeCheckerTag.USAGE then
		checker = self.usecheck
	end

	if checker[v] then
		return checker[v]
	end

	U.append(self.values, { v, tag, context })
	local i = self.graph:add_node()
	assert(i == #self.values, "Value array and node array got out of sync!")
	checker[v] = i
	return i
end

---@return Metavariable
---@param context TypecheckingContext
---@param trait boolean?
function TypeCheckerState:metavariable(context, trait)
	local i = self.graph:add_node()
	local mv = setmetatable({ value = i, usage = i, trait = trait or false }, terms.metavariable_mt)
	U.append(self.values, { mv:as_value(), TypeCheckerTag.VAR })
	assert(
		i == #self.values,
		"Value array and node array got out of sync! " .. tostring(i) .. " != " .. tostring(#self.values)
	)
	return mv
end

---@param val value
---@param use value
---@param cause any
---@return boolean
---@return ...
function TypeCheckerState:flow(val, val_context, use, use_context, cause)
	return self:constrain(val, val_context, use, use_context, UniverseOmegaRelation, cause)
end

---@param left integer
---@param right integer
---@param rel SubtypeRelation
function TypeCheckerState:check_heads(left, right, rel)
	local lvalue, ltag, lctx = table.unpack(self.values[left])
	local rvalue, rtag, rctx = table.unpack(self.values[right])

	if ltag == TypeCheckerTag.VALUE and rtag == TypeCheckerTag.USAGE then
		-- Unpacking tuples hasn't been fixed in VSCode yet (despite the issue being closed???) so we have to override the types: https://github.com/LuaLS/lua-language-server/issues/1816
		local tuple_params = value_array(value.prim(lvalue), value.prim(rvalue))
		-- TODO: how do we pass in the type contexts???
		U.tag("apply_value", { lvalue, rvalue }, apply_value, rel.constrain, value.tuple_value(tuple_params))
		-- local ok, err = U.tag(
		-- 	"check_concrete",
		-- 	{ lvalue, rvalue },
		-- 	check_concrete,
		-- 	lvalue --[[@as value]],
		-- 	rvalue --[[@as value]]
		-- )
		-- if not ok then
		-- 	error(err)
		-- end
	end
end

---@param left integer
---@param right integer
---@param rel SubtypeRelation
function TypeCheckerState:constrain_induce_call(left, right, rel)
	---@type value, TypeCheckerTag, TypecheckingContext
	local lvalue, ltag, lctx = table.unpack(self.values[left])
	---@type value, TypeCheckerTag, TypecheckingContext
	local rvalue, rtag, rctx = table.unpack(self.values[right])

	if ltag == TypeCheckerTag.VAR and lvalue:is_neutral() and lvalue:unwrap_neutral():is_application_stuck() then
		local f, arg = lvalue:unwrap_neutral():unwrap_application_stuck()
		local l = self:check_value(value.neutral(f), TypeCheckerTag.VALUE, nil)
		U.append(self.pending, EdgeNotif.CallLeft(l, arg, rel, right, "Inside constrain_induce_call ltag"))
	end

	if rtag == TypeCheckerTag.VAR and rvalue:is_neutral() and rvalue:unwrap_neutral():is_application_stuck() then
		local f, arg = rvalue:unwrap_neutral():unwrap_application_stuck()
		local r = self:check_value(value.neutral(f), TypeCheckerTag.USAGE, nil)
		U.append(self.pending, EdgeNotif.CallRight(left, rel, r, arg, "Inside constrain_induce_call rtag"))
	end
end

---check for compositions of a constrain edge and a left call edge in response to a new constrain edge
---@param left integer
---@param rel SubtypeRelation
---@param right integer
function TypeCheckerState:constrain_leftcall_compose_1(left, rel, right)
	local mvalue, mtag, mctx = table.unpack(self.values[right])
	if mtag == TypeCheckerTag.VAR then
		for _, r2 in ipairs(self.graph.leftcalldownsets[right].array) do
			if FunctionRelation(r2[3]) ~= rel then
				error("Relations do not match! " .. tostring(FunctionRelation(r2[3])) .. " is not " .. tostring(rel))
			end
			U.append(
				self.pending,
				EdgeNotif.CallLeft(left, r2[2], r2[3], r2[1], "constrain leftcall composition induced by constrain")
			)
		end
	end
end

---check for compositions of a constrain edge and a left call edge in response to a new left call edge
---@param left integer
---@param arg value
---@param rel SubtypeRelation
---@param right integer
function TypeCheckerState:constrain_leftcall_compose_2(left, arg, rel, right)
	local mvalue, mtag, mctx = table.unpack(self.values[left])
	if mtag == TypeCheckerTag.VAR then
		for _, l2 in ipairs(self.graph.upsets[left].array) do
			if l2[2] ~= FunctionRelation(rel) then
				error("Relations do not match! " .. tostring(l2[2]) .. " is not " .. tostring(FunctionRelation(rel)))
			end
			U.append(
				self.pending,
				EdgeNotif.CallLeft(left, arg, rel, l2[1], "constrain leftcall composition induced by leftcall")
			)
		end
	end
end

---check for compositions of a right call edge and a constrain edge in response to a new constrain edge
---@param left integer
---@param rel SubtypeRelation
---@param right integer
function TypeCheckerState:rightcall_constrain_compose_2(left, rel, right)
	local mvalue, mtag, mctx = table.unpack(self.values[left])
	if mtag == TypeCheckerTag.VAR then
		for _, l2 in ipairs(self.graph.rightcallupsets[left].array) do
			if FunctionRelation(l2[3]) ~= rel then
				error("Relations do not match! " .. tostring(FunctionRelation(l2[3])) .. " is not " .. tostring(rel))
			end
			U.append(
				self.pending,
				EdgeNotif.CallRight(left, l2[3], l2[1], l2[2], "rightcall constrain composition induced by constrain")
			)
		end
	end
end

---check for compositions of a right call edge and a constrain edge in response to a new right call edge
---@param left integer
---@param arg value
---@param rel SubtypeRelation
---@param right integer
function TypeCheckerState:rightcall_constrain_compose_1(left, rel, right, arg)
	local mvalue, mtag, mctx = table.unpack(self.values[right])
	if mtag == TypeCheckerTag.VAR then
		for _, r2 in ipairs(self.graph.downsets[right].array) do
			if r2[2] ~= FunctionRelation(rel) then
				error("Relations do not match! " .. tostring(r2[2]) .. " is not " .. tostring(FunctionRelation(rel)))
			end
			U.append(
				self.pending,
				EdgeNotif.CallRight(left, rel, r2[1], arg, "constrain leftcall composition induced by leftcall")
			)
		end
	end
end

---@param val value
---@param val_context TypecheckingContext
---@param use value
---@param use_context TypecheckingContext
---@param rel SubtypeRelation
---@param cause any
---@return boolean
---@return ...
function TypeCheckerState:constrain(val, val_context, use, use_context, rel, cause)
	assert(val and use, "empty val or use passed into constrain!")
	assert(#self.pending == 0, "pending not empty at start of constrain!")
	--TODO: add contexts to queue_work if appropriate
	--self:queue_work(val, val_context, use, use_context, cause)
	self:queue_constrain(val, rel, use, cause)

	while #self.pending > 0 do
		local item = U.pop(self.pending)

		if item.kind == "constrain" then
			local left, right, rel, cause = item.left, item.right, item.rel, item.cause
			if self.graph:add_constrain_edge(left, right, rel) then
				self.graph:constrain_transitivity(left, right, self.pending, rel, cause)
				U.tag("check_heads", { left, right }, self.check_heads, self, left, right, rel)
				self:constrain_induce_call(left, right, rel)
				self:constrain_leftcall_compose_1(left, rel, right)
				self:rightcall_constrain_compose_2(left, rel, right)
			end
		elseif item.kind == "call_left" then
			local left, right, rel, arg, cause = item.left, item.right, item.rel, item.arg, item.cause

			if self.graph:add_call_left_edge(left, arg, rel, right) then
				self:constrain_leftcall_compose_2(left, arg, rel, right)
			end
		elseif item.kind == "call_right" then
			local left, right, rel, arg, cause = item.left, item.right, item.rel, item.arg, item.cause

			if self.graph:add_call_right_edge(left, rel, right, arg) then
				self:rightcall_constrain_compose_1(left, rel, right, arg)
			end
		else
			error("Unknown edge kind!")
		end
	end

	assert(#self.pending == 0, "pending was not drained!")
	return true
end

local typechecker_state_mt = { __index = TypeCheckerState }

---@return TypeCheckerState
function TypeCheckerState:shadow()
	return setmetatable({
		pending = U.shadowarray(self.pending),
		graph = self.graph:shadow(),
		values = U.shadowarray(self.values),
		valcheck = U.shadowtable(self.valcheck),
		usecheck = U.shadowtable(self.usecheck),
		trait_registry = self.trait_registry:shadow(),
	}, typechecker_state_mt)
end

function TypeCheckerState:commit()
	U.commit(self.pending)
	self.graph:commit()
	U.commit(self.values)
	U.commit(self.valcheck)
	U.commit(self.usecheck)
	self.trait_registry:commit()
end

---@return TypeCheckerState
local function new_typechecker_state()
	return setmetatable({
		pending = {},
		graph = reachability(),
		values = {},
		valcheck = {},
		usecheck = {},
		trait_registry = trait_registry(),
	}, typechecker_state_mt)
end

typechecker_state = new_typechecker_state()

local evaluator = {
	typechecker_state = typechecker_state,
	extract_tuple_elem_type_closures = extract_tuple_elem_type_closures,
	const_combinator = const_combinator,
	check = check,
	infer = infer,
	infer_tuple_type = infer_tuple_type,
	evaluate = evaluate,
	apply_value = apply_value,
	index_tuple_value = index_tuple_value,
	OMEGA = OMEGA,
}
internals_interface.evaluator = evaluator

---@param fn fun() : ...
---@return boolean
---@return ...
function TypeCheckerState:speculate(fn)
	local function capture(ok, ...)
		if ok then
			-- flattens all our changes back on to self
			typechecker_state:commit()
		end
		typechecker_state = self
		evaluator.typechecker_state = self
		return ok, ...
	end
	typechecker_state = self:shadow()
	evaluator.typechecker_state = typechecker_state
	return capture(xpcall(fn, metalanguage.custom_traceback))
	--return capture(pcall(fn))
end

return evaluator
