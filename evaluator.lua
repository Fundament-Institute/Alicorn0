local terms = require "./terms"
local runtime_context = terms.runtime_context
local typechecking_context = terms.typechecking_context
local checkable_term = terms.checkable_term
local inferrable_term = terms.inferrable_term
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
local param_info_implicit = value.param_info(value.visibility(visibility.implicit))
local result_info_pure = value.result_info(result_info(purity.pure))
local result_info_effectful = value.result_info(result_info(purity.effectful))

---@param ... any
---@return value
local function tup_val(...)
	return value.tuple_value(value_array(...))
end

---@param ... any
---@return value
local function prim_tup_val(...)
	return value.prim_tuple_value(primitive_array(...))
end

local derivers = require "./derivers"
local traits = require "./traits"
local U = require "./utils"
local OMEGA = 10
local typechecker_state
local evaluate, infer, check, apply_value

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

---@param t any
---@return integer
local function get_level(t)
	-- TODO: this
	-- TODO: typecheck
	return 0
end

---@param val value an alicorn value
---@param mappings table the placeholder we are trying to get rid of by substituting
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
		for i, v in ipairs(elems) do
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

		-- TODO: deconstruct nuetral value or something
		print("nval", nval)
		error("substitute_inner not implemented yet val:is_neutral")
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
		for i, v in ipairs(family_args) do
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

local function is_type_of_types(val)
	return val:is_star() or val:is_prop() or val:is_prim_type_type()
end

local make_inner_context
local infer_tuple_type, infer_tuple_type_unwrapped
local terms = require "./terms"
local value = terms.value

local check_concrete
-- indexed by kind x kind
local concrete_comparers = {}

local function add_comparer(ka, kb, comparer)
	concrete_comparers[ka] = concrete_comparers[ka] or {}
	concrete_comparers[ka][kb] = comparer
end

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

local function always_fits_comparer(a, b, typechecker)
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
local function tuple_compare(a, b, typechecker)
	-- fixme lol
	local placeholder = value.neutral(neutral_value.free(free.unique({})))
	local tuple_types_a, na = infer_tuple_type_unwrapped(a, placeholder)
	local tuple_types_b, nb = infer_tuple_type_unwrapped(b, placeholder)
	if na ~= nb then
		return false, "tuple types have different length"
	end
	for i = 1, na do
		local ta, tb = tuple_types_a[i], tuple_types_b[i]

		if ta ~= tb then
			local ok, err
			if tb.kind == "value.neutral" then
				typechecker:queue_work(ta, tb, "Nuetral value in tuple_compare")
			else
				typechecker:queue_work(ta, tb, "tuple_compare")
			end

			if not ok then
				return false, err
			end
		end
	end
	return true
end
add_comparer("value.tuple_type", "value.tuple_type", tuple_compare)
add_comparer("value.prim_tuple_type", "value.prim_tuple_type", tuple_compare)
add_comparer("value.pi", "value.pi", function(a, b, typechecker)
	if a == b then
		return true
	end

	local avis = a.param_info.visibility.visibility
	local bvis = b.param_info.visibility.visibility
	if avis ~= bvis and avis ~= terms.visibility.implicit then
		return false, concrete_fail("pi param_info")
	end

	local apurity = a.result_info.purity
	local bpurity = b.result_info.purity
	if apurity ~= bpurity then
		return false, concrete_fail("pi result_info")
	end

	local unique_placeholder = terms.value.neutral(terms.neutral_value.free(terms.free.unique({})))
	local a_res = apply_value(a.result_type, unique_placeholder)
	local b_res = apply_value(b.result_type, unique_placeholder)
	typechecker:queue_work(a_res, b_res, "pi function results")
	typechecker:queue_work(b.param_type, a.param_type, "pi function parameters")

	return true
end)
add_comparer("value.prim_function_type", "value.prim_function_type", function(a, b, typechecker)
	if a == b then
		return true
	end

	local unique_placeholder = terms.value.neutral(terms.neutral_value.free(terms.free.unique({})))
	local a_res = apply_value(a.result_type, unique_placeholder)
	local b_res = apply_value(b.result_type, unique_placeholder)
	typechecker:queue_work(a_res, b_res, "prim function results")
	typechecker:queue_work(b.param_type, a.param_type, "prim function parameters")
	return true
end)

for _, type_of_type in ipairs({
	value.prim_type_type,
}) do
	add_comparer(type_of_type.kind, value.star(0).kind, always_fits_comparer)
end

add_comparer(value.star(0).kind, value.star(0).kind, function(a, b, typechecker)
	if a.level > b.level then
		print("star-comparer error:")
		print("a:", a.level)
		print("b:", b.level)
		return false, "a.level > b.level"
	end
	return true
end)

add_comparer("value.prim_wrapped_type", "value.prim_wrapped_type", function(a, b, typechecker)
	local ua, ub = a:unwrap_prim_wrapped_type(), b:unwrap_prim_wrapped_type()
	check_concrete(ua, ub, typechecker)
	return true
end)

-- Compares any non-metavariables, or defers any metavariable comparisons to the work queue
---@param val value
---@param use value
---@param typechecker TypeCheckerState
---@return boolean
---@return string?
function check_concrete(val, use, typechecker)
	assert(val and use, "nil value or usage passed into check_concrete!")

	if val:is_neutral() and use:is_neutral() then
		if val == use then
			return true
		end
		val:diff(use)
		return false, "both values are neutral, but they aren't equal: " .. tostring(val) .. " ~= " .. tostring(use)
	end

	if not concrete_comparers[val.kind] then
		error("No valid concrete type comparer found for value " .. val.kind)
	elseif not concrete_comparers[use.kind] then
		error("No valid concrete type comparer found for usage " .. use.kind)
	end

	local comparer = (concrete_comparers[val.kind] or {})[use.kind]
	if not comparer then
		return false, "no valid concerete comparer between value " .. val.kind .. " and usage " .. use.kind
	end

	return comparer(val, use)
end

local function extract_tuple_elem_type_closures(enum_val, closures)
	local constructor, arg = enum_val.constructor, enum_val.arg
	if constructor == "empty" then
		if #arg.elements ~= 0 then
			error "enum_value with constructor empty should have no args"
		end
		return closures
	end
	if constructor == "cons" then
		if #arg.elements ~= 2 then
			error "enum_value with constructor cons should have two args"
		end
		extract_tuple_elem_type_closures(arg.elements[1], closures)
		if not arg.elements[2]:is_closure() then
			error "second elem in tuple_type enum_value should be closure"
		end
		closures:append(arg.elements[2])
		return closures
	end
	error "unknown enum constructor for value.tuple_type's enum_value, should not be reachable"
end

value:derive(derivers.eq)

---@param checkable_term checkable
---@param typechecking_context TypecheckingContext
---@param goal_type value
---@return Array, typed
local function check(
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
			local ok, err
			if inferred_type:is_neutral() then
				ok, err = false, "inferred type is a neutral value"
				-- TODO: add debugging dump to typechecking context that looks for placeholders inside inferred_type
				-- then shows matching types and values in env if relevant?
			else
				ok, err = typechecker_state:flow(inferred_type, goal_type)
			end
			if not ok then
				print "attempting to check if terms fit for checkable_term.inferrable"
				--for i = 2, 49 do
				--	local d = debug.getinfo(i, "Sln")
				--	print(string.format("%s %s %s: %s:%d", d.what, d.namewhat, d.name, d.source, d.currentline))
				--end
				print("checkable_term", checkable_term:pretty_print(typechecking_context))
				print("inferred_type", inferred_type)
				print("goal_type", goal_type)
				print("typechecking_context", typechecking_context:format_names())
				error(
					"check: mismatch in inferred and goal type for "
						.. inferrable_term.kind
						.. " due to "
						.. tostring(err)
				)
			end
		end
		return inferred_usages, typed_term
	elseif checkable_term:is_tuple_cons() then
		local elements = checkable_term:unwrap_tuple_cons()

		local goal_tuple_type_elements = goal_type:unwrap_tuple_type()
		local elem_type_closures = extract_tuple_elem_type_closures(goal_tuple_type_elements, value_array())
		if #elem_type_closures ~= #elements then
			print("goal_type", goal_type)
			print("elements", elements)
			error("check: mismatch in checkable_term.tuple_cons goal type element count and elements in tuple cons")
		end

		local usages = usage_array()
		local new_elements = typed_array()
		local tuple_elems = value_array()
		for i, v in ipairs(elements) do
			local tuple_elem_type = apply_value(elem_type_closures[i], value.tuple_value(tuple_elems))

			local el_usages, el_term = check(v, typechecking_context, tuple_elem_type)

			add_arrays(usages, el_usages)
			new_elements:append(el_term)

			local new_elem = evaluate(el_term, typechecking_context.runtime_context)
			tuple_elems:append(new_elem)
		end
		return usages, typed_term.tuple_cons(new_elements)
	elseif checkable_term:is_prim_tuple_cons() then
		local elements = checkable_term:unwrap_prim_tuple_cons()

		local goal_tuple_type_elements = goal_type:unwrap_prim_tuple_type()
		local elem_type_closures = extract_tuple_elem_type_closures(goal_tuple_type_elements, value_array())
		if #elem_type_closures ~= #elements then
			print("goal_type", goal_type)
			print("elements", elements)
			error(
				"check: mismatch in checkable_term.prim_tuple_cons goal type element count and elements in tuple cons"
			)
		end

		local usages = usage_array()
		local new_elements = typed_array()
		local tuple_elems = value_array()
		for i, v in ipairs(elements) do
			local tuple_elem_type = apply_value(elem_type_closures[i], value.tuple_value(tuple_elems))

			local el_usages, el_term = check(v, typechecking_context, tuple_elem_type)

			add_arrays(usages, el_usages)
			new_elements:append(el_term)
			local new_elem = evaluate(el_term, typechecking_context.runtime_context)
			tuple_elems:append(new_elem)
		end
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
		return evaluate(code, capture:append(arg))
	elseif f:is_neutral() then
		return value.neutral(neutral_value.application_stuck(f:unwrap_neutral(), arg))
	elseif f:is_prim() then
		local prim_func_impl = f:unwrap_prim()
		if prim_func_impl == nil then
			error "expected to get a function but found nil, did you forget to return the function from an intrinsic"
		end
		if arg:is_prim_tuple_value() then
			local arg_elements = arg:unwrap_prim_tuple_value()
			return prim_tup_val(prim_func_impl(arg_elements:unpack()))
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
end

local function eq_prim_tuple_value_decls(left, right, typechecking_context)
	local lcons, larg = left:unwrap_enum_value()
	local rcons, rarg = right:unwrap_enum_value()
	if lcons == "empty" and rcons == "empty" then
		return typechecking_context
	elseif lcons == "empty" or rcons == "empty" then
		error(
			"eq_prim_tuple_value_decls: mismatch in number of expected and given args in primitive function application"
		)
	elseif lcons == "cons" and rcons == "cons" then
		local left_details = larg.elements
		local right_details = rarg.elements
		local context = eq_prim_tuple_value_decls(left_details[1], right_details[1], typechecking_context)
		local left_f = left_details[2]
		local right_f = right_details[2]
		local elements = value_array()
		local runtime_context = context:get_runtime_context()
		for i = #typechecking_context + 1, #context do
			elements:append(runtime_context:get(i))
		end
		local arg = value.tuple_value(elements)
		local left_type = apply_value(left_f, arg)
		local right_type = apply_value(right_f, arg)
		if left_type == right_type then
			local new_context = context:append("eq_prim_tuple_value_decls_param", left_type)
			return new_context
		else
			print("mismatch")
			print(left_type:pretty_print())
			print(right_type:pretty_print())
			error("eq_prim_tuple_value_decls: type mismatch in primitive function application")
		end
	else
		error("eq_prim_tuple_value_decls: unknown tuple type data constructor")
	end

	error("unreachable!?")
end

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
function make_inner_context(decls, tupletypes, make_prefix)
	-- evaluate the type of the tuple
	local constructor, arg = decls:unwrap_enum_value()
	if constructor == "empty" then
		return tupletypes, 0
	elseif constructor == "cons" then
		local details = arg:unwrap_tuple_value()
		local tupletypes, n_elements = make_inner_context(details[1], tupletypes, make_prefix)
		local f = details[2]
		local prefix = make_prefix(n_elements)
		local element_type = apply_value(f, prefix)
		tupletypes[#tupletypes + 1] = element_type
		return tupletypes, n_elements + 1
	else
		error("infer: unknown tuple type data constructor")
	end
end

function infer_tuple_type_unwrapped(subject_type, subject_value)
	local decls, make_prefix = make_tuple_prefix(subject_type, subject_value)
	return make_inner_context(decls, {}, make_prefix)
end

function infer_tuple_type(subject_type, subject_value)
	-- define how the type of each tuple element should be evaluated
	return infer_tuple_type_unwrapped(subject_type, subject_value)
end

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
		for i = 1, context_size do
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

		if not result_type_result_info:unwrap_result_info().purity:is_pure() then
			error "result type computation must be pure for now"
		end

		local ok, err = typechecker_state:flow(
			evaluate(param_type_term, typechecking_context.runtime_context),
			result_type_param_type,
			"inferrable pi term"
		)
		if not ok then
			error(
				"inferrable pi type's param type doesn't fit into the result type function's parameters because " .. err
			)
		end
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
			if not f_param_info:unwrap_param_info():unwrap_visibility():is_explicit() then
				error("infer: nyi implicit parameters")
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
		local type_data = value.enum_value("empty", tup_val())
		local usages = usage_array()
		local new_elements = typed_array()
		for _, v in ipairs(elements) do
			local el_type, el_usages, el_term = infer(v, typechecking_context)
			type_data = value.enum_value(
				"cons",
				tup_val(
					type_data,
					substitute_type_variables(el_type, #typechecking_context + 1, nil, typechecking_context)
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
		local type_data = value.enum_value("empty", tup_val())
		local usages = usage_array()
		local new_elements = typed_array()
		for _, v in ipairs(elements) do
			local el_type, el_usages, el_term = infer(v, typechecking_context)
			--print "inferring element of tuple construction"
			--print(el_type:pretty_print())
			type_data = value.enum_value(
				"cons",
				tup_val(
					type_data,
					substitute_type_variables(el_type, #typechecking_context + 1, nil, typechecking_context)
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
			inner_context = inner_context:append("tuple_element_" .. i, v, index_tuple_value(subject_value, i))
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
		local type_data = value.enum_value("empty", tup_val())
		local usages = usage_array()
		local new_fields = string_typed_map()
		for k, v in pairs(fields) do
			local field_type, field_usages, field_term = infer(v, typechecking_context)
			type_data = value.enum_value(
				"cons",
				tup_val(
					type_data,
					value.name(k),
					substitute_type_variables(field_type, #typechecking_context + 1, nil, typechecking_context)
				)
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
			if constructor == "empty" then
				return string_array(), string_value_map()
			elseif constructor == "cons" then
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
		local type_data = value.enum_value("empty", tup_val())
		local new_methods = string_typed_map()
		for k, v in pairs(methods) do
			local method_type, method_usages, method_term = infer(v, typechecking_context)
			type_data = value.enum_value("cons", tup_val(type_data, value.name(k), method_type))
			new_methods[k] = method_term
		end
		-- TODO: usages
		return value.object_type(type_data), usages_array(), typed_term.object_cons(new_methods)
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
		if userdata_type ~= op_userdata_type and not typechecker_state:flow(userdata_type, op_userdata_type) then
			p(userdata_type, op_userdata_type)
			print(userdata_type:pretty_print())
			print(op_userdata_type:pretty_print())
			error("infer: mismatch in userdata types of operative construction")
		end
		local operative_usages = usage_array()
		add_arrays(operative_usages, operative_type_usages)
		add_arrays(operative_usages, userdata_usages)
		return operative_type_value, operative_usages, typed_term.operative_cons(userdata_term)
	elseif inferrable_term:is_operative_type_cons() then
		local function cons(...)
			return value.enum_value("cons", tup_val(...))
		end
		local empty = value.enum_value("empty", tup_val())
		local handler, userdata_type = inferrable_term:unwrap_operative_type_cons()
		local goal_type = value.pi(
			value.tuple_type(
				cons(
					cons(
						cons(cons(empty, const_combinator(prim_syntax_type)), const_combinator(prim_environment_type)),
						const_combinator(prim_typed_term_type)
					),
					const_combinator(prim_goal_type)
				)
			),
			--unrestricted(tup_val(unrestricted(prim_syntax_type), unrestricted(prim_environment_type))),
			param_info_explicit,
			const_combinator(
				value.tuple_type(
					cons(
						cons(empty, const_combinator(prim_inferrable_term_type)),
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
		local handler_level = get_level(handler_type)
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
			local e_type, e_usages, e_term = infer(v, runtime_context)
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
		return value.prim_wrapped_type(backing_type), content_usages, typed_term.prim_wrap(content_term)
	elseif inferrable_term:is_prim_unstrict_wrap() then
		local content = inferrable_term:unwrap_prim_wrap()
		local content_type, content_usages, content_term = infer(content, typechecking_context)
		return value.prim_unstrict_wrapped_type(backing_type),
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
		local stype, susages, sterm = check(terms.value.prim_bool_type, typechecking_context, subject)
		local ctype, cusages, cterm = infer(consequent, typechecking_context)
		local atype, ausages, aterm = infer(alternate, typechecking_context)
		local restype = typechecker_state:metavariable():as_value()
		typechecker_state:flow(ctype, restype, "inferred prim if consequent")
		typechecker_state:flow(atype, restype, "inferred prim if alternate")

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
		local arg_type_a, arg_usages_a, arg_term_a = infer(inferrable_term.level_a, typechecking_context)
		local arg_type_b, arg_usages_b, arg_term_b = infer(inferrable_term.level_b, typechecking_context)
		return value.level_type, usage_array(), typed_term.level_max(arg_term_a, arg_term_b)
	elseif inferrable_term:is_level_suc() then
		local arg_type, arg_usages, arg_term = infer(inferrable_term.previous_level, typechecking_context)
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

	--[[
  if inferrable_term.kind == "inferrable_level0" then
    return value.level_type, typed_term.level0
  elseif inferrable_term.kind == "inferrable_level_suc" then
    local arg_type, arg_term = infer(inferrable_term.previous_level, typechecking_context)
    arg_type:unify(value.level_type)
    return value.level_type, typed_term.level_suc(arg_term)
  elseif inferrable_term.kind == "inferrable_level_max" then
    local arg_type_a, arg_term_a = infer(inferrable_term.level_a, typechecking_context)
    local arg_type_b, arg_term_b = infer(inferrable_term.level_b, typechecking_context)
    arg_type_a:unify(value.level_type)
    arg_type_b:unify(value.level_type)
    return value.level_type, typed_term.level_max(arg_term_a, arg_term_b)
  elseif inferrable_term.kind == "inferrable_level_type" then
    return value.star(0), typed_term.level_type
  elseif inferrable_term.kind == "inferrable_star" then
    return value.star(1), typed_term.star(0)
  elseif inferrable_term.kind == "inferrable_prop" then
    return value.star(1), typed_term.prop(0)
  elseif inferrable_term.kind == "inferrable_prim" then
    return value.star(1), typed_term.prim
  end
  ]]
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
		return apply_value(f_value, arg_value)
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
			for i = real_length + 1, length do
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
		local previous_level = evaluate(typed_term.previous_level, runtime_context)
		if not previous_level:is_level() then
			p(previous_level)
			error "wrong type for previous_level"
		end
		if previous_level.level > OMEGA then
			error("NYI: level too high for typed_level_suc" .. tostring(previous_level.level))
		end
		return value.level(previous_level.level + 1)
	elseif typed_term:is_level_max() then
		local level_a = evaluate(typed_term.level_a, runtime_context)
		local level_b = evaluate(typed_term.level_b, runtime_context)
		if not level_a:is_level() or not level_b:is_level() then
			error "wrong type for level_a or level_b"
		end
		return value.level(math.max(level_a.level, level_b.level))
	elseif typed_term:is_level_type() then
		return value.level_type
	elseif typed_term:is_star() then
		return value.star(typed_term.level)
	elseif typed_term:is_prop() then
		return value.prop(typed_term.level)
	elseif typed_term:is_prim_tuple_type() then
		local decl = typed_term:unwrap_prim_tuple_type()
		local decl_val = evaluate(decl, runtime_context)
		return value.prim_tuple_type(decl_val)
	else
		error("evaluate: unknown kind: " .. typed_term.kind)
	end

	error("unreachable!?")

	--[[
  if typed_term.kind == "typed_level0" then
    return value.level(0)
  elseif typed_term.kind == "typed_level_suc" then
    local previous_level = evaluate(typed_term.previous_level, runtime_context)
    if previous_level.kind ~= "value_level" then
      p(previous_level)
      error("wrong type for previous_level")
    end
    if previous_level.level > OMEGA then
      error("NYI: level too high for typed_level_suc" .. tostring(previous_level.level))
    end
    return value.level(previous_level.level + 1)
  elseif typed_term.kind == "typed_level_max" then
    local level_a = evaluate(typed_term.level_a, runtime_context)
    local level_b = evaluate(typed_term.level_b, runtime_context)
    if level_a.kind ~= "value_level" or level_b.kind ~= "value_level" then
      error("wrong type for level_a or level_b")
    end
    return value.level(math.max(level_a.level, level_b.level))
  elseif typed_term.kind == "typed_level_type" then
    return value.level_type
  elseif typed_term.kind == "typed_star" then
    return value.star(typed_term.level)
  elseif typed_term.kind == "typed_prop" then
    return value.prop(typed_term.level)
  elseif typed_term.kind == "typed_prim" then
    return value.prim
  end
  ]]
end

---@class OrderedSet
---@field set { [any]: integer }
---@field array any[]
local OrderedSet = {}

---@param t any
---@return boolean
function OrderedSet:insert(t)
	if self.set[t] == nil then
		return false
	end
	self.set[t] = #self.array + 1
	table.insert(self.array, t)
	return true
end

---@param t any
---@return boolean
function OrderedSet:insert_aux(t, ...)
	if self.set[t] == nil then
		return false
	end
	self.set[t] = #self.array + 1
	table.insert(self.array, { t, ... })
	return true
end

local ordered_set_mt = { __index = OrderedSet }

---@return OrderedSet
local function ordered_set()
	return setmetatable({ set = {}, count = 0 }, ordered_set_mt)
end

---@class TypeCheckerState
---@field pending table
---@field graph Reachability
---@field values table
---@field valcheck table
---@field usecheck table
local TypeCheckerState = {}

---@class Reachability
---@field upsets OrderedSet[]
---@field downsets OrderedSet[]
local Reachability = {}

---@return integer
function Reachability:add_node()
	local i = #self.upsets + 1 -- Account for lua tables starting at 1
	table.insert(self.upsets, ordered_set())
	table.insert(self.downsets, ordered_set())
	assert(#self.upsets == #self.downsets, "upsets must equal downsets!")
	return i
end

---@param left integer
---@param right integer
---@param queue table
---@param context any
function Reachability:add_edge(left, right, queue, context)
	assert(type(left) == "number", "left isn't an integer!")
	assert(type(right) == "number", "left isn't an integer!")
	local work = { { left, right } }

	while #work > 0 do
		local l, r = table.unpack(table.remove(work))

		assert(self.downsets[l], "Can't find " .. tostring(l))
		if self.downsets[l]:insert(r) then
			assert(self.downsets[r], "Can't find " .. tostring(r))
			self.upsets[r]:insert(l)
			table.insert(queue, { l, r })

			for i, l2 in ipairs(self.upsets[l].array) do
				table.insert(work, { l2, r })
			end
			for i, r2 in ipairs(self.downsets[r].array) do
				table.insert(work, { l, r2 })
			end
		end
	end
end

local reachability_mt = { __index = Reachability }

---@return Reachability
local function reachability()
	return setmetatable({ downsets = {}, upsets = {} }, reachability_mt)
end

---@class TypeCheckerTag
local TypeCheckerTag = {
	VALUE = {},
	USAGE = {},
	VAR = {},
}
---@param val value
---@param use value
---@param context any
function TypeCheckerState:queue_work(val, use, context)
	local l = self:check_value(val, TypeCheckerTag.VALUE)
	local r = self:check_value(use, TypeCheckerTag.USAGE)
	assert(type(l) == "number", "l isn't number, instead found " .. tostring(l))
	assert(type(r) == "number", "r isn't number, instead found " .. tostring(r))
	table.insert(self.pending, { l, r, context })
end

---@param v value
---@param tag TypeCheckerTag
---@return integer
function TypeCheckerState:check_value(v, tag)
	if v:is_neutral() and v:unwrap_neutral():is_free() and v:unwrap_neutral():unwrap_free():is_metavariable() then
		local mv = v:unwrap_neutral():unwrap_free():unwrap_metavariable()
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

	table.insert(self.values, { v, tag })
	local i = self.graph:add_node()
	assert(i == #self.values, "Value array and node array got out of sync!")
	checker[v] = i
	return i
end

---@return Metavariable
function TypeCheckerState:metavariable()
	local i = self.graph:add_node()
	local mv = setmetatable({ value = i, usage = i }, terms.metavariable_mt)
	table.insert(self.values, { mv:as_value(), TypeCheckerTag.VAR })
	assert(i == #self.values, "Value array and node array got out of sync!")
	return mv
end

---@param val value
---@param use value
---@param context any
function TypeCheckerState:flow(val, use, context)
	assert(#self.pending == 0, "pending not empty at start of flow!")
	self:queue_work(val, use, context)
	local queue = {}

	while #self.pending > 0 do
		local left, right, context = table.unpack(table.remove(self.pending))
		self.graph:add_edge(left, right, queue, context)

		-- Check if adding that edge resulted in any new type pairs needing to be checked
		while #queue > 0 do
			local l, r = table.unpack(table.remove(queue))

			local lvalue, ltag = table.unpack(self.values[l])
			local rvalue, rtag = table.unpack(self.values[r])
			if ltag == TypeCheckerTag.VALUE and rtag == TypeCheckerTag.USAGE then
				check_concrete(lvalue, rvalue, self)
			end
		end
	end

	assert(#queue == 0, "queue was not empty after flow!")
	assert(#self.pending == 0, "pending was not drained!")
	return true
end

local typechecker_state_mt = { __index = TypeCheckerState }

---@return TypeCheckerState
local function new_typechecker_state()
	return setmetatable({
		pending = {},
		graph = reachability(),
		values = {},
		valcheck = {},
		usecheck = {},
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
return evaluator
