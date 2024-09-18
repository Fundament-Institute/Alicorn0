local terms = require "terms"
local metalanguage = require "metalanguage"
local U = require "alicorn-utils"
local runtime_context = terms.runtime_context
local s = require "pretty-printer".s
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
local host_syntax_type = terms.host_syntax_type
local host_environment_type = terms.host_environment_type
local host_typed_term_type = terms.host_typed_term_type
local host_goal_type = terms.host_goal_type
local host_inferrable_term_type = terms.host_inferrable_term_type

local gen = require "terms-generators"
local map = gen.declare_map
local string_typed_map = map(gen.builtin_string, typed_term)
local string_value_map = map(gen.builtin_string, value)
local array = gen.declare_array
local typed_array = array(typed_term)
local value_array = array(value)
local host_array = array(gen.any_lua_type)
local usage_array = array(gen.builtin_number)
local string_array = array(gen.builtin_string)

local internals_interface = require "internals-interface"

local eval_types = require "evaluator-types"
local subtype_relation_mt, SubtypeRelation, EdgeNotif =
	eval_types.subtype_relation_mt, eval_types.SubtypeRelation, eval_types.EdgeNotif

local param_info_explicit = value.param_info(value.visibility(visibility.explicit))
local result_info_pure = value.result_info(result_info(purity.pure))

local OMEGA = 10
local typechecker_state
local evaluate, infer, check, apply_value
local name_array = string_array
local typed = terms.typed_term

---@param luafunc function
---@return value
local function luatovalue(luafunc)
	local luafunc_debug = debug.getinfo(luafunc, "u")
	local parameters = name_array()
	local len = luafunc_debug.nparams
	local new_body = typed_array()

	for i = 1, len do
		parameters:append(debug.getlocal(luafunc, i))
		new_body:append(typed.bound_variable(i + 1))
	end

	return value.closure(
		"#luatovalue-args",
		typed.application(
			typed.literal(value.host_value(luafunc)),
			typed.tuple_elim(parameters, typed.bound_variable(1), len, typed.host_tuple_cons(new_body))
		),
		runtime_context()
	)
end

---@param srel SubtypeRelation
---@return SubtypeRelation
local function FunctionRelation(srel)
	return setmetatable({
		debug_name = "FunctionRelation(" .. srel.debug_name .. ")",
		srel = srel,
		Rel = luatovalue(function(a, b)
			error("nyi")
		end),
		refl = luatovalue(function(a)
			error("nyi")
		end),
		antisym = luatovalue(function(a, b, r1, r2)
			error("nyi")
		end),
		constrain = luatovalue(function(lctx, val, rctx, use)
			local u = value.neutral(
				neutral_value.free(free.unique({ debug = "FunctionRelation(" .. srel.debug_name .. ").constrain" }))
			)

			local applied_val = U.tag("apply_value", { val = val, use = use }, apply_value, val, u)
			local applied_use = U.tag("apply_value", { val = val, use = use }, apply_value, use, u)

			typechecker_state:queue_constrain(lctx, applied_val, srel, rctx, applied_use, "FunctionRelation inner")
		end),
	}, subtype_relation_mt)
end
FunctionRelation = U.memoize(FunctionRelation)

---@param ... Variance
---@return SubtypeRelation
local function IndepTupleRelation(...)
	local args = { ... }
	local names = {}
	for i, v in ipairs(args) do
		names[i] = (v.positive and "+" or "-") .. v.srel.debug_name
	end
	return setmetatable({
		debug_name = "IndepTupleRelation(" .. table.concat(names, ", ") .. ")",
		srels = args,
		Rel = luatovalue(function(a, b)
			error("nyi")
		end),
		refl = luatovalue(function(a)
			error("nyi")
		end),
		antisym = luatovalue(function(a, b, r1, r2)
			error("nyi")
		end),
		constrain = luatovalue(
			---constrain tuple elements
			---@param lctx TypecheckingContext
			---@param val value
			---@param rctx TypecheckingContext
			---@param use value
			function(lctx, val, rctx, use)
				local val_elems = val:unwrap_tuple_value()
				local use_elems = use:unwrap_tuple_value()
				for i = 1, val_elems:len() do
					if args[i].positive then
						typechecker_state:queue_constrain(
							lctx,
							val_elems[i],
							args[i].srel,
							rctx,
							use_elems[i],
							"tuple element constraint"
						)
					else
						typechecker_state:queue_constrain(
							rctx,
							use_elems[i],
							args[i].srel,
							lctx,
							val_elems[i],
							"tuple element constraint"
						)
					end
				end
			end
		),
	}, subtype_relation_mt)
end
IndepTupleRelation = U.memoize(IndepTupleRelation)

---@type SubtypeRelation
local effect_row_srel
effect_row_srel = setmetatable({
	debug_name = "effect_row_srel",
	Rel = luatovalue(function(a, b)
		error("nyi")
	end),
	refl = luatovalue(function(a)
		error("nyi")
	end),
	antisym = luatovalue(function(a, b, r1, r2)
		error("nyi")
	end),

	constrain = luatovalue(
		---@param lctx TypecheckingContext
		---@param val value
		---@param rctx TypecheckingContext
		---@param use value
		function(lctx, val, rctx, use)
			if val:is_effect_empty() then
				return true
			end
			if val:is_effect_row() then
				local val_components, val_rest = val:unwrap_effect_row()
				if use:is_effect_empty() then
					error "production has effect requirements that the consumption doesn't fulfill"
				end
				if not use:is_effect_row() then
					error "consumption of effect row constraint isn't an effect row?"
				end
				local use_components, use_rest = use:unwrap_effect_row()
				if not use_components:superset(val_components) then
					error "consumption of effect row doesn't satisfy all components of production"
				end
				--TODO allow polymorphism
				if val_rest:is_effect_empty() and use_rest:is_effect_empty() then
					return true
				end
				error "NYI effect polymorphism"
			end
		end
	),
}, subtype_relation_mt)

---@type SubtypeRelation
local UniverseOmegaRelation

---@type SubtypeRelation
local enum_desc_srel
enum_desc_srel = setmetatable({
	debug_name = "enum_desc_srel",
	Rel = luatovalue(function(a, b)
		error("nyi")
	end),
	refl = luatovalue(function(a)
		error("nyi")
	end),
	antisym = luatovalue(function(a, b, r1, r2)
		error("nyi")
	end),

	constrain = luatovalue(
		---@param lctx TypecheckingContext
		---@param val value
		---@param rctx TypecheckingContext
		---@param use value
		function(lctx, val, rctx, use)
			if not val:is_enum_desc_value() then
				error "production is not an enum description"
			end
			local val_variants = val:unwrap_enum_desc_value()
			if not use:is_enum_desc_value() then
				error "consumption is not an enum description"
			end
			local use_variants = use:unwrap_enum_desc_value()
			for name, use_type in use_variants:pairs() do
				typechecker_state:queue_subtype(
					lctx,
					val_variants:get(name) --[[@as value -- please find a better approach]],
					rctx,
					use_type,
					"enum variant"
				)
			end
		end
	),
}, subtype_relation_mt)

local infer_tuple_type_unwrapped2, substitute_type_variables
---@type SubtypeRelation
local TupleDescRelation = setmetatable({
	debug_name = "TupleDescRelation",
	Rel = luatovalue(function(a, b)
		error("nyi")
	end),
	refl = luatovalue(function(a)
		error("nyi")
	end),
	antisym = luatovalue(function(a, b, r1, r2)
		error("nyi")
	end),
	constrain = luatovalue(
		---@param lctx TypecheckingContext
		---@param val value
		---@param rctx TypecheckingContext
		---@param use value
		function(lctx, val, rctx, use)
			-- FIXME: this should probably be handled elsewhere
			if val:is_neutral() and val == use then
				return
			end
			-- FIXME: this is quick'n'dirty copypaste, slightly edited to jankily call existing code
			-- this HAPPENS to work
			-- this WILL need to be refactored
			-- i have considered exploiting the linked-list structure of tuple desc for recursive
			-- checking, but doing it naively won't work because the unique (representing the tuple
			-- value) should be the same across the whole desc
			local unique = { debug = "TupleDescRelation.constrain" }
			local placeholder = value.neutral(neutral_value.free(free.unique(unique)))
			local tuple_types_val, tuple_types_use, tuple_vals, n =
				infer_tuple_type_unwrapped2(value.tuple_type(val), value.tuple_type(use), placeholder)
			for i = 1, n do
				typechecker_state:queue_subtype(
					lctx,
					tuple_types_val[i],
					rctx,
					tuple_types_use[i],
					"TupleDescRelation.constrain"
				)
			end
		end
	),
}, subtype_relation_mt)

---@param onto ArrayValue
---@param with ArrayValue
local function add_arrays(onto, with)
	local olen = onto:len()
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
		local unique = { debug = "substitute_inner, val:is_closure" }
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
		local desc = val:unwrap_tuple_type()
		local desc = substitute_inner(desc, mappings, context_len)
		return typed_term.tuple_type(desc)
	elseif val:is_tuple_desc_type() then
		return typed_term.literal(val)
	elseif val:is_enum_value() then
		local constructor, arg = val:unwrap_enum_value()
		local arg = substitute_inner(arg, mappings, context_len)
		return typed_term.enum_cons(constructor, arg)
	elseif val:is_enum_type() then
		local desc = val:unwrap_enum_type()
		-- TODO: Handle desc properly, because it's a value.
		return typed_term.literal(val)
	elseif val:is_record_value() then
		-- TODO: How to deal with a map?
		error("Records not yet implemented")
	elseif val:is_record_type() then
		local desc = val:unwrap_record_type()
		-- TODO: Handle desc properly, because it's a value.
		error("Records not yet implemented")
	elseif val:is_record_extend_stuck() then
		-- Needs to handle the nuetral value and map of values
		error("Records not yet implemented")
	elseif val:is_srel_type() then
		local target = val:unwrap_srel_type()
		local target_sub = substitute_inner(target, mappings, context_len)
		return typed_term.srel_type(target_sub)
	elseif val:is_variance_type() then
		local target = val:unwrap_variance_type()
		local target_sub = substitute_inner(target, mappings, context_len)
		return typed_term.variance_type(target_sub)
	elseif val:is_object_value() then
		return typed_term.literal(val)
	elseif val:is_object_type() then
		-- local desc = val:unwrap_object_type()
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
				local mv = free:unwrap_metavariable()

				if not (mv.block_level < typechecker_state.block_level) then
					return typechecker_state:slice_constraints_for(mv, mappings, context_len)
				else
					lookup = free:unwrap_metavariable()
				end
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

		if nval:is_host_unwrap_stuck() then
			local boxed = nval:unwrap_host_unwrap_stuck()
			return typed_term.host_unwrap(substitute_inner(value.neutral(boxed), mappings, context_len))
		end

		if nval:is_host_wrap_stuck() then
			local to_wrap = nval:unwrap_host_wrap_stuck()
			return typed_term.host_wrap(substitute_inner(value.neutral(to_wrap), mappings, context_len))
		end

		if nval:is_host_unwrap_stuck() then
			local to_unwrap = nval:unwrap_host_unwrap_stuck()
			return typed_term.host_unwrap(substitute_inner(value.neutral(to_unwrap), mappings, context_len))
		end

		if nval:is_host_application_stuck() then
			local fn, arg = nval:unwrap_host_application_stuck()
			return typed_term.application(
				typed_term.literal(value.host_value(fn)),
				substitute_inner(value.neutral(arg), mappings, context_len)
			)
		end

		if nval:is_host_tuple_stuck() then
			local leading, stuck, trailing = nval:unwrap_host_tuple_stuck()
			local elems = typed_array()
			-- leading is an array of unwrapped host_values and must already be unwrapped host values
			for _, elem in ipairs(leading) do
				local elem_value = typed_term.literal(value.host_value(elem))
				elems:append(elem_value)
			end
			elems:append(substitute_inner(value.neutral(stuck), mappings, context_len))
			for _, elem in ipairs(trailing) do
				elems:append(substitute_inner(elem, mappings, context_len))
			end
			-- print("host_tuple_stuck nval", nval)
			local result = typed_term.host_tuple_cons(elems)
			-- print("host_tuple_stuck result", result)
			return result
		end

		if nval:is_host_if_stuck() then
			local subject, consequent, alternate = nval:unwrap_host_if_stuck()
			local subject = substitute_inner(value.neutral(subject), mappings, context_len)
			local consequent = substitute_inner(consequent, mappings, context_len)
			local alternate = substitute_inner(alternate, mappings, context_len)
			return typed_term.host_if(subject, consequent, alternate)
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
	elseif val:is_host_value() then
		return typed_term.literal(val)
	elseif val:is_host_type_type() then
		return typed_term.literal(val)
	elseif val:is_host_number_type() then
		return typed_term.literal(val)
	elseif val:is_host_bool_type() then
		return typed_term.literal(val)
	elseif val:is_host_string_type() then
		return typed_term.literal(val)
	elseif val:is_host_function_type() then
		local param_type, result_type, resinfo = val:unwrap_host_function_type()
		local param_type = substitute_inner(param_type, mappings, context_len)
		local result_type = substitute_inner(result_type, mappings, context_len)
		local resinfo = substitute_inner(resinfo, mappings, context_len)
		return typed_term.host_function_type(param_type, result_type, resinfo)
	elseif val:is_host_wrapped_type() then
		local type = val:unwrap_host_wrapped_type()
		local type = substitute_inner(type, mappings, context_len)
		return typed_term.host_wrapped_type(type)
	elseif val:is_host_user_defined_type() then
		local id, family_args = val:unwrap_host_user_defined_type()
		local res = typed_array()
		for _, v in ipairs(family_args) do
			res:append(substitute_inner(v, mappings, context_len))
		end
		return typed_term.host_user_defined_type_cons(id, res)
	elseif val:is_host_nil_type() then
		return typed_term.literal(val)
	elseif val:is_host_tuple_value() then
		return typed_term.literal(val)
	elseif val:is_host_tuple_type() then
		local desc = val:unwrap_host_tuple_type()
		local desc = substitute_inner(desc, mappings, context_len)
		return typed_term.host_tuple_type(desc)
	elseif val:is_range() then
		local lower_bounds, upper_bounds, relation = val:unwrap_range()
		local sub_lower_bounds = typed_array()
		local sub_upper_bounds = typed_array()
		for _, v in ipairs(lower_bounds) do
			local sub = substitute_inner(v, mappings, context_len)
			sub_lower_bounds:append(sub)
		end
		for _, v in ipairs(upper_bounds) do
			local sub = substitute_inner(v, mappings, context_len)
			sub_upper_bounds:append(sub)
		end
		local sub_relation = substitute_inner(relation, mappings, context_len)
		return typed_term.range(sub_lower_bounds, sub_upper_bounds, sub_relation)
	elseif val:is_singleton() then
		local supertype, val = val:unwrap_singleton()
		local supertype = substitute_inner(supertype, mappings, context_len)
		return typed_term.singleton(supertype, val)
	elseif val:is_union_type() then
		local a, b = val:unwrap_union_type()
		return typed_term.union_type(
			substitute_inner(a, mappings, context_len),
			substitute_inner(b, mappings, context_len)
		)
	elseif val:is_intersection_type() then
		local a, b = val:unwrap_intersection_type()
		return typed_term.intersection_type(
			substitute_inner(a, mappings, context_len),
			substitute_inner(b, mappings, context_len)
		)
	else
		error("Unhandled value kind in substitute_inner: " .. val.kind)
	end
end

--for substituting a single var at index
---@param val value
---@param index integer
---@param param_name string?
---@return value
function substitute_type_variables(val, index, param_name)
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
	return val:is_star() or val:is_prop() or val:is_host_type_type()
end

local make_inner_context
local infer_tuple_type, infer_tuple_type_unwrapped
local make_inner_context2
local infer_tuple_type2

local check_concrete
-- indexed by kind x kind
---@type {[string] : {[string] : value_comparer}}
local concrete_comparers = {}

---collapse accessor paths into concrete type bounds
---@param ctx TypecheckingContext
---@param typ value
---@return TypecheckingContext, value
local function revealing(ctx, typ)
	if not typ:is_neutral() then
		return ctx, typ
	end

	local nv = typ:unwrap_neutral()

	if nv:is_tuple_element_access_stuck() then
		local subject, elem = nv:unwrap_tuple_element_access_stuck()
		if subject:is_free() then
			local var = subject:unwrap_free()
			if var:is_placeholder() then
				local idx, dbg = var:unwrap_placeholder()
				local inner = ctx:get_type(idx)
				local inner_bound = value.tuple_type(typechecker_state:metavariable(ctx, false):as_value())
				print("found inner", inner)
				error "FINISH THIS"
			end
		else
			error "NYI, revealing a tuple access that isn't on a variable"
		end
	end
	error "NYI, revealing something that isn't a tuple access"
end

---take apart a symbolic tuple value to produce a (simplified? hopefully?) prefix suitable for use in upcasting and downcasting
---@param subject value
---@param idx integer
---@return value
local function tuple_slice(subject, idx)
	if subject:is_neutral() then
		local nv = subject:unwrap_neutral()
		if nv:is_free() then
			return subject
		end
	end
	error "NYI any other tuple plsfix" --FIXME --TODO
end

---extract a specified element type from a given tuple desc
---@param subject value
---@param desc value
---@param idx integer
---@return value
local function extract_desc_nth(subject, desc, idx)
	local slices = {}
	repeat
		local variant, args = desc:unwrap_enum_value()
		local done = false
		if variant == terms.DescCons.empty then
			done = true
		elseif variant == terms.DescCons.cons then
			local pfx, elem = args:unwrap_tuple_value():unpack()
			slices[#slices + 1] = elem
			desc = pfx
		else
			error "unknown constructor; broken tuple desc?"
		end
	until done

	if #slices < idx then
		error("tuple is too short for specified index " .. tostring(#slices) .. " < " .. tostring(idx))
	end
	local type_former = slices[#slices - idx + 1]
	local prefix = tuple_slice(subject, idx)
	local elem_type = apply_value(type_former, prefix)
	return elem_type
end

---@param ctx TypecheckingContext
---@param typ value
---@return TypecheckingContext, value
local function upcast(ctx, typ)
	if not typ:is_neutral() then
		return ctx, typ
	end

	local nv = typ:unwrap_neutral()

	if nv:is_tuple_element_access_stuck() then
		local subject, elem = nv:unwrap_tuple_element_access_stuck()
		if subject:is_free() then
			local var = subject:unwrap_free()
			if var:is_placeholder() then
				local idx, dbg = var:unwrap_placeholder()
				local inner = ctx:get_type(idx)
				--local inner_bound = value.tuple_type(typechecker_state:metavariable(ctx, false):as_value())
				local context2, boundstype = revealing(ctx, inner)
				--TODO: speculate for bottom
				--TODO: speculate on tuple type and reformulate extraction in terms of constraining
				if boundstype:is_tuple_type() then
					local desc = boundstype:unwrap_tuple_type()
					local member = extract_desc_nth(value.neutral(subject), desc, elem)
					--TODO: level srel? speculate on member types?
					if member:is_star() then
						local level, depth = member:unwrap_star()
						if depth > 0 then
							return ctx, value.star(level - 1, depth - 1)
						end
					end
				end
			end
		end
	end
	error "NYI upcast something or other"
end

---@alias value_comparer fun(lctx: TypecheckingContext, a: value, rctx: TypecheckingContext, b: value): boolean, (string|ConcreteFail)?

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
local function always_fits_comparer(lctx, a, rctx, b)
	return true
end

-- host types
for _, host_type in ipairs({
	value.host_number_type,
	value.host_string_type,
	value.host_bool_type,
	value.host_user_defined_type({ name = "" }, value_array()),
}) do
	add_comparer(host_type.kind, host_type.kind, always_fits_comparer)
end

-- types of types
add_comparer(value.host_type_type.kind, value.host_type_type.kind, always_fits_comparer)
add_comparer("value.tuple_type", "value.tuple_type", function(lctx, a, rctx, b)
	local desc_a = a:unwrap_tuple_type()
	local desc_b = b:unwrap_tuple_type()
	typechecker_state:queue_constrain(lctx, desc_a, TupleDescRelation, rctx, desc_b, "tuple type")
	return true
end)
add_comparer("value.host_tuple_type", "value.host_tuple_type", function(lctx, a, rctx, b)
	local desc_a = a:unwrap_host_tuple_type()
	local desc_b = b:unwrap_host_tuple_type()
	typechecker_state:queue_constrain(lctx, desc_a, TupleDescRelation, rctx, desc_b, "host tuple type")
	return true
end)
add_comparer("value.enum_desc_type", "value.enum_desc_type", function(lctx, a, rctx, b)
	local a_univ = a:unwrap_enum_desc_type()
	local b_univ = b:unwrap_enum_desc_type()
	typechecker_state:queue_subtype(lctx, a_univ, rctx, b_univ, "enum desc universe covariance")
	return true
end)
add_comparer("value.enum_type", "value.enum_type", function(lctx, a, rctx, b)
	local a_desc = a:unwrap_enum_type()
	local b_desc = b:unwrap_enum_type()
	typechecker_state:queue_constrain(lctx, a_desc, enum_desc_srel, rctx, b_desc, "enum type description")
	return true
end)
add_comparer("value.pi", "value.pi", function(lctx, a, rctx, b)
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

	typechecker_state:queue_subtype(rctx, b_param_type, lctx, a_param_type, "pi function parameters")
	--local unique_placeholder = terms.value.neutral(terms.neutral_value.free(terms.free.unique({})))
	--local a_res = apply_value(a_result_type, unique_placeholder)
	--local b_res = apply_value(b_result_type, unique_placeholder)
	--typechecker_state:queue_constrain(a_res, FunctionRelation(UniverseOmegaRelation), b_res, "pi function results")

	--TODO implement the SA-ALL rule which is slightly more powerful than this rule
	typechecker_state:queue_constrain(
		lctx,
		a_result_type,
		FunctionRelation(UniverseOmegaRelation),
		rctx,
		b_result_type,
		"pi function results"
	)

	return true
end)
add_comparer("value.host_function_type", "value.host_function_type", function(lctx, a, rctx, b)
	if a == b then
		return true
	end

	local a_param_type, a_result_type, a_result_info = a:unwrap_host_function_type()
	local b_param_type, b_result_type, b_result_info = b:unwrap_host_function_type()

	local apurity = a_result_info:unwrap_result_info():unwrap_result_info()
	local bpurity = b_result_info:unwrap_result_info():unwrap_result_info()
	if apurity ~= bpurity then
		return false, concrete_fail("host function result_info")
	end

	typechecker_state:queue_subtype(rctx, b_param_type, lctx, a_param_type, "host function parameters")
	--local unique_placeholder = terms.value.neutral(terms.neutral_value.free(terms.free.unique({})))
	--local a_res = apply_value(a_result_type, unique_placeholder)
	--local b_res = apply_value(b_result_type, unique_placeholder)
	--typechecker_state:queue_constrain(b_res, FunctionRelation(UniverseOmegaRelation), a_res, "host function parameters")

	--TODO implement the SA-ALL rule which is slightly more powerful than this rule
	typechecker_state:queue_constrain(
		lctx,
		a_result_type,
		FunctionRelation(UniverseOmegaRelation),
		rctx,
		b_result_type,
		"host function results"
	)
	return true
end)

---@type {[table] : SubtypeRelation}
local host_srel_map = {}
add_comparer("value.host_user_defined_type", "value.host_user_defined_type", function(lctx, a, rctx, b)
	local a_id, a_args = a:unwrap_host_user_defined_type()
	local b_id, b_args = b:unwrap_host_user_defined_type()

	if not a_id == b_id then
		error(
			"ids do not match in host user defined types: "
				.. a_id.name
				.. "("
				.. tostring(a_id)
				.. ") ~= "
				.. b_id.name
				.. "("
				.. tostring(b_id)
				.. ")"
		)
	end
	if not host_srel_map[a_id] then
		error("No variance specified for user defined host type " .. a_id.name)
	end
	apply_value(
		host_srel_map[a_id].constrain,
		value.tuple_value(
			value_array(
				value.host_value(lctx),
				value.host_value(value.tuple_value(a_args)),
				value.host_value(rctx),
				value.host_value(value.tuple_value(b_args))
			)
		)
	)
	return true
end)

---define subtyping for a user defined host type
---@param id table
---@param rel SubtypeRelation
local function register_host_srel(id, rel)
	host_srel_map[id] = rel
end

for i, host_type in ipairs {
	terms.host_syntax_type,
	terms.host_environment_type,
	terms.host_typed_term_type,
	terms.host_goal_type,
	terms.host_inferrable_term_type,
	terms.host_checkable_term_type,
	terms.host_lua_error_type,
} do
	local id, family_args = host_type:unwrap_host_user_defined_type()
	register_host_srel(id, IndepTupleRelation())
end

add_comparer("value.srel_type", "value.srel_type", function(lctx, a, rctx, b)
	local a_target = a:unwrap_srel_type()
	local b_target = b:unwrap_srel_type()
	typechecker_state:queue_subtype(lctx, a_target, rctx, b_target, "srel target")
	return true
end)

add_comparer("value.variance_type", "value.variance_type", function(lctx, a, rctx, b)
	local a_target = a:unwrap_variance_type()
	local b_target = b:unwrap_variance_type()
	typechecker_state:queue_subtype(lctx, a_target, rctx, b_target, "variance target")
	return true
end)

for _, type_of_type in ipairs({
	value.host_type_type,
}) do
	add_comparer(type_of_type.kind, value.star(0, 0).kind, always_fits_comparer)
end

add_comparer(value.star(0, 0).kind, value.star(0, 0).kind, function(lctx, a, rctx, b)
	local alevel, adepth = a:unwrap_star()
	local blevel, bdepth = b:unwrap_star()
	if alevel > blevel then
		print("star-comparer error:")
		print("a level:", alevel)
		print("b level:", blevel)
		return false, "a.level > b.level"
	end
	if adepth < bdepth then
		print("star-comparer error:")
		print("a depth:", adepth)
		print("b depth:", bdepth)
		return false, "a.depth < b.depth"
	end
	return true
end)

add_comparer("value.host_wrapped_type", "value.host_wrapped_type", function(lctx, a, rctx, b)
	local ua, ub = a:unwrap_host_wrapped_type(), b:unwrap_host_wrapped_type()
	typechecker_state:queue_subtype(lctx, ua, rctx, ub, "wrapped type target")
	--U.tag("check_concrete", { ua, ub }, check_concrete, ua, ub)
	return true
end)

add_comparer("value.singleton", "value.singleton", function(lctx, a, rctx, b)
	local a_supertype, a_value = a:unwrap_singleton()
	local b_supertype, b_value = b:unwrap_singleton()
	typechecker_state:queue_subtype(lctx, a_supertype, rctx, b_supertype, "singleton supertypes")

	if a_value == b_value then
		return true
	else
		return false, "unequal singletons"
	end
end)

add_comparer("value.tuple_desc_type", "value.tuple_desc_type", function(lctx, a, rctx, b)
	local a_universe = a:unwrap_tuple_desc_type()
	local b_universe = b:unwrap_tuple_desc_type()
	typechecker_state:queue_subtype(lctx, a_universe, rctx, b_universe, "tuple_desc_type universes")
	return true
end)

add_comparer("value.program_type", "value.program_type", function(lctx, a, rctx, b)
	local a_eff, a_base = a:unwrap_program_type()
	local b_eff, b_base = b:unwrap_program_type()
	typechecker_state:queue_subtype(lctx, a_base, rctx, b_base, "program result")
	typechecker_state:queue_constrain(lctx, a_eff, effect_row_srel, rctx, b_eff, "program effects")
	return true
end)

add_comparer("value.effect_row_type", "value.effect_row_type", function(lctx, a, rctx, b)
	return true
end)
add_comparer("value.effect_type", "value.effect_type", function(lctx, a, rctx, b)
	return true
end)

-- Compares any non-metavariables, or defers any metavariable comparisons to the work queue
---@param val value
---@param use value
---@return boolean
---@return string?
function check_concrete(lctx, val, rctx, use)
	assert(val and use, "nil value or usage passed into check_concrete!")

	if val:is_neutral() and use:is_neutral() then
		if val == use then
			return true
		end
		--TODO: enable the x.A <: y.A case
		return false, "both values are neutral, but they aren't equal: " .. tostring(val) .. " ~= " .. tostring(use)
	end

	if val:is_neutral() then
		local vnv = val:unwrap_neutral()
		if vnv:is_tuple_element_access_stuck() then
			local innerctx, bound = upcast(lctx, val)
			typechecker_state:queue_subtype(innerctx, bound, rctx, use)
			return true
		end
	end

	if val:is_singleton() and not use:is_singleton() then
		local val_supertype, _ = val:unwrap_singleton()
		typechecker_state:queue_subtype(lctx, val_supertype, rctx, use, "singleton subtype")
		return true
	end

	if val:is_union_type() then
		local vala, valb = val:unwrap_union_type()
		typechecker_state:queue_subtype(lctx, vala, rctx, use, "union dissasembly")
		typechecker_state:queue_subtype(lctx, valb, rctx, use, "union dissasembly")
		return true
	end

	if use:is_intersection_type() then
		local usea, useb = use:unwrap_intersection_type()
		typechecker_state:queue_subtype(lctx, val, rctx, usea, "intersection dissasembly")
		typechecker_state:queue_subtype(lctx, val, rctx, useb, "intersection dissasembly")
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

	return comparer(lctx, val, rctx, use)
end

---@param enum_val value
---@param closures ArrayValue
---@return ArrayValue
local function extract_tuple_elem_type_closures(enum_val, closures)
	local constructor, arg = enum_val:unwrap_enum_value()
	local elements = arg:unwrap_tuple_value()
	if constructor == terms.DescCons.empty then
		if elements:len() ~= 0 then
			error "enum_value with constructor empty should have no args"
		end
		return closures
	end
	if constructor == terms.DescCons.cons then
		if elements:len() ~= 2 then
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
---@return ArrayValue, typed
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
		local desc = terms.empty

		for _, v in ipairs(elements) do
			local el_type_metavar = typechecker_state:metavariable(typechecking_context)
			local el_type = el_type_metavar:as_value()
			local el_usages, el_term = check(v, typechecking_context, el_type)

			add_arrays(usages, el_usages)
			new_elements:append(el_term)

			local el_val = evaluate(el_term, typechecking_context.runtime_context)

			desc = terms.cons(
				desc,
				value.closure(
					"#check-tuple-cons-param",
					typed_term.literal(value.singleton(el_type, el_val)),
					typechecking_context.runtime_context
				)
			)
		end

		typechecker_state:flow(
			value.tuple_type(desc),
			typechecking_context,
			goal_type,
			typechecking_context,
			"checkable_term:is_tuple_cons"
		)

		return usages, typed_term.tuple_cons(new_elements)
	elseif checkable_term:is_host_tuple_cons() then
		local elements = checkable_term:unwrap_host_tuple_cons()
		local usages = usage_array()
		local new_elements = typed_array()
		local desc = terms.empty

		for _, v in ipairs(elements) do
			local el_type_metavar = typechecker_state:metavariable(typechecking_context)
			local el_type = el_type_metavar:as_value()
			local el_usages, el_term = check(v, typechecking_context, el_type)

			add_arrays(usages, el_usages)
			new_elements:append(el_term)

			local el_val = evaluate(el_term, typechecking_context.runtime_context)

			desc = terms.cons(
				desc,
				value.closure(
					"#check-tuple-cons-param",
					typed_term.literal(value.singleton(el_type, el_val)),
					typechecking_context.runtime_context
				)
			)
		end

		typechecker_state:flow(
			value.host_tuple_type(desc),
			typechecking_context,
			goal_type,
			typechecking_context,
			"checkable_term:is_host_tuple_cons"
		)

		return usages, typed_term.host_tuple_cons(new_elements)
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
		--return U.notail(U.tag("evaluate", { code = code }, evaluate, code, capture:append(arg)))
		return evaluate(code, capture:append(arg))
	elseif f:is_neutral() then
		return value.neutral(neutral_value.application_stuck(f:unwrap_neutral(), arg))
	elseif f:is_host_value() then
		local host_func_impl = f:unwrap_host_value()
		if host_func_impl == nil then
			error "expected to get a function but found nil, did you forget to return the function from an intrinsic"
		end
		if arg:is_host_tuple_value() then
			local arg_elements = arg:unwrap_host_tuple_value()
			return value.host_tuple_value(host_array(host_func_impl(arg_elements:unpack())))
		elseif arg:is_neutral() then
			return value.neutral(neutral_value.host_application_stuck(host_func_impl, arg:unwrap_neutral()))
		else
			error("apply_value, is_host_value, arg: expected a host tuple argument")
		end
	else
		error("apply_value, f: expected a function/closure, but got " .. tostring(f))
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
	elseif subject:is_host_tuple_value() then
		local elems = subject:unwrap_host_tuple_value()
		return value.host_value(elems[index])
	elseif subject:is_neutral() then
		local inner = subject:unwrap_neutral()
		if inner:is_host_tuple_stuck() then
			local leading, stuck_elem, trailing = inner:unwrap_host_tuple_stuck()
			if leading:len() >= index then
				return terms.value.host_value(leading[index])
			elseif leading:len() + 1 == index then
				return terms.value.neutral(stuck_elem)
			elseif leading:len() + 1 + trailing:len() >= index then
				return trailing[index - leading:len() - 1]
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
	local desc, make_prefix
	if subject_type:is_tuple_type() then
		desc = subject_type:unwrap_tuple_type()

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
			error(
				"make_tuple_prefix, is_tuple_type, subject_value: expected a tuple, instead got "
					.. subject_value:pretty_print()
			)
		end
	elseif subject_type:is_host_tuple_type() then
		desc = subject_type:unwrap_host_tuple_type()

		if subject_value:is_host_tuple_value() then
			local subject_elements = subject_value:unwrap_host_tuple_value()
			local subject_value_elements = value_array()
			for _, v in ipairs(subject_elements) do
				subject_value_elements:append(value.host_value(v))
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
			error(
				"make_tuple_prefix, is_host_tuple_type, subject_value: expected a host tuple, instead got "
					.. subject_value:pretty_print()
			)
		end
	else
		print(subject_type:pretty_print())
		error("make_tuple_prefix, subject_type: expected a term with a tuple type, but got " .. subject_type.kind)
	end

	return desc, make_prefix
end

-- TODO: create a typechecking context append variant that merges two
---@param desc value
---@param make_prefix fun(i: integer): value
---@return value[]
---@return integer
---@return value[]
function make_inner_context(desc, make_prefix)
	-- evaluate the type of the tuple
	local constructor, arg = desc:unwrap_enum_value()
	if constructor == terms.DescCons.empty then
		return value_array(), 0, value_array()
	elseif constructor == terms.DescCons.cons then
		local details = arg:unwrap_tuple_value()
		local tupletypes, n_elements, tuplevals = make_inner_context(details[1], make_prefix)
		local f = details[2]
		local element_type
		if tupletypes:len() == tuplevals:len() then
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
	local desc, make_prefix = make_tuple_prefix(subject_type, subject_value)
	return make_inner_context(desc, make_prefix)
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

---@param desc_a value
---@param make_prefix_a fun(i: integer): value
---@param desc_b value
---@param make_prefix_b fun(i: integer): value
---@return value[]
---@return value[]
---@return value[]
---@return integer
function make_inner_context2(desc_a, make_prefix_a, desc_b, make_prefix_b)
	local constructor_a, arg_a = desc_a:unwrap_enum_value()
	local constructor_b, arg_b = desc_b:unwrap_enum_value()
	if constructor_a == terms.DescCons.empty and constructor_b == terms.DescCons.empty then
		return value_array(), value_array(), value_array(), 0
	elseif constructor_a == terms.DescCons.empty or constructor_b == terms.DescCons.empty then
		error("tuple desc lengths must be equal")
	elseif constructor_a == terms.DescCons.cons and constructor_b == terms.DescCons.cons then
		local details_a = arg_a:unwrap_tuple_value()
		local details_b = arg_b:unwrap_tuple_value()
		local tupletypes_a, tupletypes_b, tuplevals, n_elements =
			make_inner_context2(details_a[1], make_prefix_a, details_b[1], make_prefix_b)
		local f_a = details_a[2]
		local f_b = details_b[2]
		local element_type_a
		local element_type_b
		if tupletypes_a:len() == tuplevals:len() then
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
	local desc_a, make_prefix_a = make_tuple_prefix(subject_type_a, subject_value)
	local desc_b, make_prefix_b = make_tuple_prefix(subject_type_b, subject_value)
	return make_inner_context2(desc_a, make_prefix_a, desc_b, make_prefix_b)
end

---@param typ value
---@return integer
local function nearest_star_level(typ)
	if typ:is_host_type_type() then
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
---@return value, ArrayValue, typed
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
		local context_size = typechecking_context:len()
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

		local result_type = U.tag(
			"substitute_type_variables",
			{ body_type = body_type, index = inner_context:len(), block_level = typechecker_state.block_level },
			substitute_type_variables,
			body_type,
			inner_context:len(),
			param_name
		)
		--print("INFER ANNOTATED LAMBDA")
		--print("result_type")
		--print(result_type:pretty_print(typechecking_context))
		local body_usages_param = body_usages[body_usages:len()]
		local lambda_usages = body_usages:copy(1, body_usages:len() - 1)
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
		local sort =
			value.union_type(param_type_type, value.union_type(result_type_result_type_result, value.star(0, 0)))
		-- local sort = value.star(
		-- 	math.max(nearest_star_level(param_type_type), nearest_star_level(result_type_result_type_result), 0)
		-- )

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
						"calling function with implicit args, result type applied on implicit args must be a function type: "
							.. metaresult:pretty_print()
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
				error(
					"calling function with implicit args, result type applied on implicit args must be a function type: "
						.. application_result_type:pretty_print()
				)
			end
			return application_result_type, application_usages, application
		elseif f_type:is_host_function_type() then
			local f_param_type, f_result_type_closure, f_result_info = f_type:unwrap_host_function_type()

			local arg_usages, arg_term = check(arg, typechecking_context, f_param_type)

			local application_usages = usage_array()
			add_arrays(application_usages, f_usages)
			add_arrays(application_usages, arg_usages)
			local application = typed_term.application(f_term, arg_term)

			-- check already checked for us so no check_concrete
			local f_result_type =
				apply_value(f_result_type_closure, evaluate(arg_term, typechecking_context:get_runtime_context()))
			if value.value_check(f_result_type) ~= true then
				error("application_result_type isn't a value inferring application of host_function_type")
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
			local el_singleton = value.singleton(el_type, el_val)
			type_data = terms.cons(type_data, substitute_type_variables(el_singleton, typechecking_context:len() + 1))
			add_arrays(usages, el_usages)
			new_elements:append(el_term)
		end
		return value.tuple_type(type_data), usages, typed_term.tuple_cons(new_elements)
	elseif inferrable_term:is_host_tuple_cons() then
		--print "inferring tuple construction"
		--print(inferrable_term:pretty_print())
		--print "environment_names"
		--for i = 1, #typechecking_context do
		--	print(i, typechecking_context:get_name(i))
		--end
		local elements = inferrable_term:unwrap_host_tuple_cons()
		-- type_data is either "empty", an empty tuple,
		-- or "cons", a tuple with the previous type_data and a function that
		-- takes all previous values and produces the type of the next element
		-- TODO: it is a type error to put something that isn't a host_value into a host tuple
		local type_data = terms.empty
		local usages = usage_array()
		local new_elements = typed_array()
		for _, v in ipairs(elements) do
			local el_type, el_usages, el_term = infer(v, typechecking_context)
			--print "inferring element of tuple construction"
			--print(el_type:pretty_print())
			local el_val = evaluate(el_term, typechecking_context.runtime_context)
			local el_singleton = value.singleton(el_type, el_val)
			type_data = terms.cons(type_data, substitute_type_variables(el_singleton, typechecking_context:len() + 1))
			add_arrays(usages, el_usages)
			new_elements:append(el_term)
		end
		return value.host_tuple_type(type_data), usages, typed_term.host_tuple_cons(new_elements)
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
		local desc = inferrable_term:unwrap_tuple_type()
		local desc_type, desc_usages, desc_term = infer(desc, typechecking_context)
		if not desc_type:is_tuple_desc_type() then
			error "argument to tuple_type is not a tuple_desc"
		end
		return terms.value.star(0, 0), desc_usages, terms.typed_term.tuple_type(desc_term)
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
				substitute_type_variables(field_type, typechecking_context:len() + 1)
			)
			add_arrays(usages, field_usages)
			new_fields[k] = field_term
		end
		return value.record_type(type_data), usages, typed_term.record_cons(new_fields)
	elseif inferrable_term:is_record_elim() then
		local subject, field_names, body = inferrable_term:unwrap_record_elim()
		local subject_type, subject_usages, subject_term = infer(subject, typechecking_context)
		local ok, desc = subject_type:as_record_type()
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
		local function make_type(desc)
			local constructor, arg = desc:unwrap_enum_value()
			if constructor == terms.DescCons.empty then
				return string_array(), string_value_map()
			elseif constructor == terms.DescCons.cons then
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
		local desc_field_names, desc_field_types = make_type(desc)

		-- reorder the fields into the requested order
		local inner_context = typechecking_context
		for _, v in ipairs(field_names) do
			local t = desc_field_types[v]
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
		-- TODO: check arg_type against enum_type desc
		return enum_type, arg_usages, typed_term.enum_cons(constructor, arg_term)
	elseif inferrable_term:is_enum_elim() then
		local subject, mechanism = inferrable_term:unwrap_enum_elim()
		local subject_type, subject_usages, subject_term = infer(subject, typechecking_context)
		-- local ok, desc = subject_type:as_enum_type()
		-- if not ok then
		--   error("infer, is_enum_elim, subject_type: expected a term with an enum type")
		-- end
		local mechanism_type, mechanism_usages, mechanism_term = infer(mechanism, typechecking_context)
		-- TODO: check subject desc against mechanism desc
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
				terms.tuple_desc(
					const_combinator(host_syntax_type),
					const_combinator(host_environment_type),
					const_combinator(host_typed_term_type),
					const_combinator(host_goal_type)
				)
			),
			--unrestricted(tup_val(unrestricted(host_syntax_type), unrestricted(host_environment_type))),
			param_info_explicit,
			const_combinator(
				value.tuple_type(
					terms.tuple_desc(
						const_combinator(host_inferrable_term_type),
						const_combinator(host_environment_type)
					)
				)
			),
			--unrestricted(tup_val(unrestricted(host_inferrable_term_type), unrestricted(host_environment_type))),
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
		return value.star(operative_type_level, 0),
			operative_type_usages,
			typed_term.operative_type_cons(handler_term, userdata_type_term)
	elseif inferrable_term:is_host_user_defined_type_cons() then
		local id, family_args = inferrable_term:unwrap_host_user_defined_type_cons()
		local new_family_args = typed_array()
		local result_usages = usage_array()
		for _, v in ipairs(family_args) do
			local e_type, e_usages, e_term = infer(v, typechecking_context)
			-- FIXME: use e_type?
			add_arrays(result_usages, e_usages)
			new_family_args:append(e_term)
		end
		return value.host_type_type, result_usages, typed_term.host_user_defined_type_cons(id, new_family_args)
	elseif inferrable_term:is_host_wrapped_type() then
		local type_inf = inferrable_term:unwrap_host_wrapped_type()
		local content_type_type, content_type_usages, content_type_term = infer(type_inf, typechecking_context)
		if not is_type_of_types(content_type_type) then
			error "infer: type being boxed must be a type"
		end
		return value.host_type_type, content_type_usages, typed_term.host_wrapped_type(content_type_term)
	elseif inferrable_term:is_host_wrap() then
		local content = inferrable_term:unwrap_host_wrap()
		local content_type, content_usages, content_term = infer(content, typechecking_context)
		return value.host_wrapped_type(content_type), content_usages, typed_term.host_wrap(content_term)
	elseif inferrable_term:is_host_unstrict_wrap() then
		local content = inferrable_term:unwrap_host_wrap()
		local content_type, content_usages, content_term = infer(content, typechecking_context)
		return value.host_unstrict_wrapped_type(content_type),
			content_usages,
			typed_term.host_unstrict_wrap(content_term)
	elseif inferrable_term:is_host_unwrap() then
		local container = inferrable_term:unwrap_host_unwrap()
		local container_type, container_usages, container_term = infer(container, typechecking_context)
		local content_type = container_type:unwrap_host_wrapped_type()
		return content_type, container_usages, typed_term.host_unwrap(container_term)
	elseif inferrable_term:is_host_unstrict_unwrap() then
		local container = inferrable_term:unwrap_host_unwrap()
		local container_type, container_usages, container_term = infer(container, typechecking_context)
		local content_type = container_type:unwrap_host_unstrict_wrapped_type()
		return content_type, container_usages, typed_term.host_unstrict_unwrap(container_term)
	elseif inferrable_term:is_host_if() then
		local subject, consequent, alternate = inferrable_term:unwrap_host_if()
		-- for each thing in typechecking context check if it == the subject, replace with literal true
		-- same for alternate but literal false

		-- TODO: Replace this with a metavariable that both branches are put into
		local susages, sterm = check(subject, typechecking_context, terms.value.host_bool_type)
		local ctype, cusages, cterm = infer(consequent, typechecking_context)
		local atype, ausages, aterm = infer(alternate, typechecking_context)
		local restype = typechecker_state:metavariable(typechecking_context):as_value()
		typechecker_state:flow(
			ctype,
			typechecking_context,
			restype,
			typechecking_context,
			"inferred host if consequent"
		)
		typechecker_state:flow(atype, typechecking_context, restype, typechecking_context, "inferred host if alternate")

		local result_usages = usage_array()
		add_arrays(result_usages, susages)
		-- FIXME: max of cusages and ausages rather than adding?
		add_arrays(result_usages, cusages)
		add_arrays(result_usages, ausages)
		return restype, result_usages, typed_term.host_if(sterm, cterm, aterm)
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
	elseif inferrable_term:is_host_intrinsic() then
		local source, type, anchor = inferrable_term:unwrap_host_intrinsic()
		local source_usages, source_term = check(source, typechecking_context, value.host_string_type)
		local type_type, type_usages, type_term = infer(type, typechecking_context) --check(type, typechecking_context, value.qtype_type(0))

		--print("host intrinsic is inferring: (inferrable term follows)")
		--print(type:pretty_print(typechecking_context))
		--print("lowers to: (typed term follows)")
		--print(type_term:pretty_print(typechecking_context))
		--error "weird type"
		-- FIXME: type_type, source_type are ignored, need checked?
		local type_val = evaluate(type_term, typechecking_context.runtime_context)
		return type_val, source_usages, typed_term.host_intrinsic(source_term, anchor)
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
	elseif inferrable_term:is_host_function_type() then
		local args, returns, resinfo = inferrable_term:unwrap_host_function_type()
		local arg_type, arg_usages, arg_term = infer(args, typechecking_context)
		local return_type, return_usages, return_term = infer(returns, typechecking_context)
		local resinfo_usages, resinfo_term = check(resinfo, typechecking_context, value.result_info_type)
		local res_usages = usage_array()
		add_arrays(res_usages, arg_usages)
		add_arrays(res_usages, return_usages)
		add_arrays(res_usages, resinfo_usages)
		return value.host_type_type, res_usages, typed_term.host_function_type(arg_term, return_term, resinfo_term)
	elseif inferrable_term:is_host_tuple_type() then
		local desc = inferrable_term:unwrap_host_tuple_type()
		local desc_type, desc_usages, desc_term = infer(desc, typechecking_context)
		if not desc_type:is_tuple_desc_type() then
			error "must be a tuple desc"
		end
		return value.star(0, 0), desc_usages, typed_term.host_tuple_type(desc_term)
	elseif inferrable_term:is_program_sequence() then
		local first, anchor, continue = inferrable_term:unwrap_program_sequence()
		local first_type, first_usages, first_term = infer(first, typechecking_context)
		if not first_type:is_program_type() then
			error("program sequence must infer to a program type")
		end
		local first_effect_sig, first_base_type = first_type:unwrap_program_type()
		local inner_context = typechecking_context:append("#program-sequence", first_base_type, nil, anchor)
		local continue_type, continue_usages, continue_term = infer(continue, inner_context)
		if not continue_type:is_program_type() then
			error(
				"rest of the program sequence must infer to a program type: "
					.. continue:pretty_print(inner_context)
					.. "\nbut it infers to "
					.. continue_type:pretty_print()
			)
		end
		local continue_effect_sig, continue_base_type = continue_type:unwrap_program_type()
		local first_is_row, first_components, first_rest = first_effect_sig:as_effect_row()
		local continue_is_row, continue_components, continue_rest = continue_effect_sig:as_effect_row()
		local result_effect_sig
		if first_is_row and continue_is_row then
			if not first_rest:is_effect_empty() or not continue_rest:is_effect_empty() then
				error("nyi polymorphic effects")
			end
			result_effect_sig = value.effect_row(first_components:union(continue_components), value.effect_empty)
		elseif first_is_row then
			if not continue_effect_sig:is_effect_empty() then
				error("unknown effect sig")
			end
			result_effect_sig = first_effect_sig
		elseif continue_is_row then
			if not first_effect_sig:is_effect_empty() then
				error("unknown effect sig")
			end
			result_effect_sig = continue_effect_sig
		else
			if not first_effect_sig:is_effect_empty() or not continue_effect_sig:is_effect_empty() then
				error("unknown effect sig")
			end
			result_effect_sig = value.effect_empty
		end
		local result_usages = usage_array()
		add_arrays(result_usages, first_usages)
		add_arrays(result_usages, continue_usages)
		return value.program_type(result_effect_sig, continue_base_type),
			result_usages,
			typed_term.program_sequence(first_term, continue_term)
	elseif inferrable_term:is_program_end() then
		local result = inferrable_term:unwrap_program_end()
		local program_type, program_usages, program_term = infer(result, typechecking_context)
		return value.program_type(value.effect_empty, program_type),
			program_usages,
			typed_term.program_end(program_term)
	elseif inferrable_term:is_program_type() then
		local effect_type, result_type = inferrable_term:unwrap_program_type()
		local effect_type_type, effect_type_usages, effect_type_term = infer(effect_type, typechecking_context)
		local result_type_type, result_type_usages, result_type_term = infer(result_type, typechecking_context)
		local res_usages = usage_array()
		add_arrays(res_usages, effect_type_usages)
		add_arrays(res_usages, result_type_usages)
		-- TODO: use biunification constraints for start level
		return value.star(0, 0), res_usages, typed_term.program_type(effect_type_term, result_type_term)
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
		local param_type_value = U.tag("evaluate", { param_type = param_type }, evaluate, param_type, runtime_context)
		local param_info_value = U.tag("evaluate", { param_info = param_info }, evaluate, param_info, runtime_context)
		local result_type_value =
			U.tag("evaluate", { result_type = result_type }, evaluate, result_type, runtime_context)
		local result_info_value =
			U.tag("evaluate", { result_info = result_info }, evaluate, result_info, runtime_context)
		return value.pi(param_type_value, param_info_value, result_type_value, result_info_value)
	elseif typed_term:is_application() then
		local f, arg = typed_term:unwrap_application()
		local f_value = U.tag("evaluate", { f = f }, evaluate, f, runtime_context)
		local arg_value = U.tag("evaluate", { arg = arg }, evaluate, arg, runtime_context)
		return U.notail(apply_value(f_value, arg_value))
		-- if you want to debug things that go through this call, you may comment above and uncomment below
		-- but beware that this single change has caused tremendous performance degradation
		-- on the order of 20x slower
		--return U.notail(
		--	U.tag("apply_value", { f_value = f_value, arg_value = arg_value }, apply_value, f_value, arg_value)
		--)
	elseif typed_term:is_tuple_cons() then
		local elements = typed_term:unwrap_tuple_cons()
		local new_elements = value_array()
		for i, v in ipairs(elements) do
			new_elements:append(U.tag("evaluate", { ["element_" .. tostring(i)] = v }, evaluate, v, runtime_context))
		end
		return value.tuple_value(new_elements)
	elseif typed_term:is_host_tuple_cons() then
		local elements = typed_term:unwrap_host_tuple_cons()
		local new_elements = host_array()
		local stuck = false
		local stuck_element
		local trailing_values
		for i, v in ipairs(elements) do
			local element_value = U.tag("evaluate", { ["element_" .. tostring(i)] = v }, evaluate, v, runtime_context)
			if element_value == nil then
				p("wtf", v.kind)
			end
			if stuck then
				trailing_values:append(element_value)
			elseif element_value:is_host_value() then
				new_elements:append(element_value:unwrap_host_value())
			elseif element_value:is_neutral() then
				stuck = true
				stuck_element = element_value:unwrap_neutral()
				trailing_values = value_array()
			else
				print("term that fails", typed_term)
				print("which element", i)
				print("element_value", element_value)
				error("evaluate, is_host_tuple_cons, element_value: expected a host value")
			end
		end
		if stuck then
			return value.neutral(neutral_value.host_tuple_stuck(new_elements, stuck_element, trailing_values))
		else
			return value.host_tuple_value(new_elements)
		end
	elseif typed_term:is_tuple_elim() then
		local names, subject, length, body = typed_term:unwrap_tuple_elim()
		local subject_value = U.tag("evaluate", { subject = subject }, evaluate, subject, runtime_context)
		local inner_context = runtime_context
		if subject_value:is_tuple_value() then
			local subject_elements = subject_value:unwrap_tuple_value()
			if subject_elements:len() ~= length then
				print("tuple has only", subject_elements:len(), "elements but expected", length)
				print("tuple being eliminated", subject_value)
				error("evaluate: mismatch in tuple length from typechecking and evaluation")
			end
			for i = 1, length do
				inner_context = inner_context:append(subject_elements[i])
			end
		elseif subject_value:is_host_tuple_value() then
			local subject_elements = subject_value:unwrap_host_tuple_value()
			local real_length = subject_elements:len()
			if real_length ~= length then
				print("evaluating typed tuple_elim error")
				print("got, expected:")
				print(subject_elements:len(), length)
				print("names:")
				print(names:pretty_print())
				print("subject:")
				print(subject:pretty_print(runtime_context))
				print("subject value:")
				--print(subject_value:pretty_print(runtime_context))
				print("<redacted>")
				print("body:")
				print(body:pretty_print(runtime_context))
				print("error commented out to allow for variable-length host tuples via the host-unit hack")
				print("if you're having issues check this!!!")
				--error("evaluate: mismatch in tuple length from typechecking and evaluation")
			end
			for i = 1, real_length do
				inner_context = inner_context:append(value.host_value(subject_elements[i]))
			end
			for _ = real_length + 1, length do
				inner_context = inner_context:append(value.host_value(nil))
			end
		elseif subject_value:is_neutral() then
			for i = 1, length do
				inner_context = inner_context:append(index_tuple_value(subject_value, i))
			end
		else
			p(subject_value)
			error("evaluate, is_tuple_elim, subject_value: expected a tuple")
		end
		return U.tag("evaluate", { body = body }, evaluate, body, inner_context)
	elseif typed_term:is_tuple_element_access() then
		local tuple_term, index = typed_term:unwrap_tuple_element_access()
		--print("tuple_element_access tuple_term: (typed term follows)")
		--print(tuple_term:pretty_print(runtime_context))
		local tuple = U.tag("evaluate", { tuple_term = tuple_term }, evaluate, tuple_term, runtime_context)
		--print("tuple_element_access tuple: (value term follows)")
		--print(tuple)
		return index_tuple_value(tuple, index)
	elseif typed_term:is_tuple_type() then
		local desc_term = typed_term:unwrap_tuple_type()
		local desc = U.tag("evaluate", { desc_term = desc_term }, evaluate, desc_term, runtime_context)
		return terms.value.tuple_type(desc)
	elseif typed_term:is_record_cons() then
		local fields = typed_term:unwrap_record_cons()
		local new_fields = string_value_map()
		for k, v in pairs(fields) do
			new_fields[k] = U.tag("evaluate", { ["record_field_" .. tostring(k)] = v }, evaluate, v, runtime_context)
		end
		return value.record_value(new_fields)
	elseif typed_term:is_record_elim() then
		local subject, field_names, body = typed_term:unwrap_record_elim()
		local subject_value = U.tag("evaluate", { subject = subject }, evaluate, subject, runtime_context)
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
		return U.tag("evaluate", { body = body }, evaluate, body, inner_context)
	elseif typed_term:is_enum_cons() then
		local constructor, arg = typed_term:unwrap_enum_cons()
		local arg_value = U.tag("evaluate", { arg = arg }, evaluate, arg, runtime_context)
		return value.enum_value(constructor, arg_value)
	elseif typed_term:is_enum_elim() then
		local subject, mechanism = typed_term:unwrap_enum_elim()
		local subject_value = U.tag("evaluate", { subject = subject }, evaluate, subject, runtime_context)
		local mechanism_value = U.tag("evaluate", { mechanism = mechanism }, evaluate, mechanism, runtime_context)
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
	elseif typed_term:is_enum_desc_cons() then
		local variants, rest = typed_term:unwrap_enum_desc_cons()
		local result = string_value_map()
		for k, v in variants:pairs() do
			local v_res = evaluate(v, runtime_context)
			result:set(k, v_res)
		end
		local res_rest = evaluate(rest, runtime_context)
		if res_rest:is_enum_desc_value() then
			local variants_rest = res_rest:unwrap_enum_desc_value()
			return value.enum_desc_value(result:union(variants_rest, function(a, b)
				return a
			end))
		else
			error "non-concrete enum desc in rest slot, TODO"
		end
	elseif typed_term:is_enum_type() then
		local desc = typed_term:unwrap_enum_type()
		local desc_val = evaluate(desc, runtime_context)
		return value.enum_type(desc_val)
	elseif typed_term:is_enum_case() then
		local target, variants, default = typed_term:unwrap_enum_case()
		local target_val = evaluate(target, runtime_context)
		if target_val:is_enum_value() then
			local variant, arg = target_val:unwrap_enum_value()
			if variants[variant] then
				return evaluate(variants[variant], runtime_context:append(arg))
			else
				return evaluate(default, runtime_context:append(target_val))
			end
		else
			error "enum case expression didn't evaluate to an enum_value"
		end
	elseif typed_term:is_enum_absurd() then
		local target, debug = typed_term:unwrap_enum_absurd()
		error("ENUM ABSURD OCCURRED: " .. debug)
	elseif typed_term:is_variance_cons() then
		local positive, srel = typed_term:unwrap_variance_cons()
		local positive_value = U.tag("evaluate", { positive = positive }, evaluate, positive, runtime_context)
		local srel_value = U.tag("evaluate", { srel = srel }, evaluate, srel, runtime_context)
		---@type Variance
		local variance = {
			positive = positive_value:unwrap_host_value(),
			srel = srel_value:unwrap_host_value(),
		}
		return value.host_value(variance)
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
	elseif typed_term:is_host_user_defined_type_cons() then
		local id, family_args = typed_term:unwrap_host_user_defined_type_cons()
		local new_family_args = value_array()
		for _, v in ipairs(family_args) do
			new_family_args:append(evaluate(v, runtime_context))
		end
		return value.host_user_defined_type(id, new_family_args)
	elseif typed_term:is_host_wrapped_type() then
		local type_term = typed_term:unwrap_host_wrapped_type()
		local type_value = evaluate(type_term, runtime_context)
		return value.host_wrapped_type(type_value)
	elseif typed_term:is_host_unstrict_wrapped_type() then
		local type_term = typed_term:unwrap_host_unstrict_wrapped_type()
		local type_value = evaluate(type_term, runtime_context)
		return value.host_wrapped_type(type_value)
	elseif typed_term:is_host_wrap() then
		local content = typed_term:unwrap_host_wrap()
		return value.host_value(content_val)
	elseif typed_term:is_host_unwrap() then
		local unwrapped = typed_term:unwrap_host_unwrap()
		local unwrap_val = evaluate(unwrapped, runtime_context)
		if not unwrap_val.as_host_value then
			print("unwrapped", unwrapped, unwrap_val)
			error "evaluate, is_host_unwrap: missing as_host_value on unwrapped host_unwrap"
		end
		if unwrap_val:is_host_value() then
			return unwrap_val:unwrap_host_value()
		elseif unwrap_val:is_neutral() then
			local nval = unwrap_val:unwrap_neutral()
			if nval:is_host_wrap_stuck() then
				return value.neutral(nval:unwrap_host_wrap_stuck())
			else
				return value.neutral(neutral_value.host_unwrap_stuck(nval))
			end
		else
			print("unrecognized value in unbox", unwrap_val)
			error "invalid value in unbox, must be host_value or neutral"
		end
	elseif typed_term:is_host_unstrict_unwrap() then
		local unwrapped = typed_term:unwrap_host_unstrict_unwrap()
		local unwrap_val = evaluate(unwrapped, runtime_context)
		if not unwrap_val.as_host_value then
			print("unwrapped", unwrapped, unwrap_val)
			error "evaluate, is_host_unwrap: missing as_host_value on unwrapped host_unwrap"
		end
		if unwrap_val:is_host_value() then
			return unwrap_val:unwrap_host_value()
		elseif unwrap_val:is_neutral() then
			local nval = unwrap_val:unwrap_neutral()
			return value.neutral(neutral_value.host_unwrap_stuck(nval))
		else
			print("unrecognized value in unbox", unwrap_val)
			error "invalid value in unbox, must be host_value or neutral"
		end
	elseif typed_term:is_host_if() then
		local subject, consequent, alternate = typed_term:unwrap_host_if()
		local sval = evaluate(subject, runtime_context)
		if sval:is_host_value() then
			local sbool = sval:unwrap_host_value()
			if type(sbool) ~= "boolean" then
				error("subject of host_if must be a host bool")
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
				inner_context_c = inner_context_c:set(index, value.host_value(true))
				inner_context_a = inner_context_a:set(index, value.host_value(false))
			end
			local cval = evaluate(consequent, inner_context_c)
			local aval = evaluate(alternate, inner_context_a)
			return value.neutral(neutral_value.host_if_stuck(sval_neutral, cval, aval))
		else
			error("subject of host_if must be host_value or neutral")
		end
	elseif typed_term:is_let() then
		local name, expr, body = typed_term:unwrap_let()
		local expr_value = evaluate(expr, runtime_context)
		return evaluate(body, runtime_context:append(expr_value))
	elseif typed_term:is_host_intrinsic() then
		local source, anchor = typed_term:unwrap_host_intrinsic()
		local source_val = evaluate(source, runtime_context)
		if source_val:is_host_value() then
			local source_str = source_val:unwrap_host_value()
			if intrinsic_memo[source_str] then
				return value.host_value(intrinsic_memo[source_str])
			end
			local load_env = {}
			for k, v in pairs(_G) do
				load_env[k] = v
			end
			for k, v in pairs(internals_interface) do
				load_env[k] = v
			end
			--local require_generator = require "require"
			--load_env.require = require_generator(anchor.sourceid)
			local res = assert(load(source_str, "host_intrinsic", "t", load_env))()
			intrinsic_memo[source_str] = res
			return value.host_value(res)
		elseif source_val:is_neutral() then
			local source_neutral = source_val:unwrap_neutral()
			return value.neutral(neutral_value.host_intrinsic_stuck(source_neutral, anchor))
		else
			error "Tried to load an intrinsic with something that isn't a string"
		end
	elseif typed_term:is_host_function_type() then
		local args, returns, resinfo = typed_term:unwrap_host_function_type()
		local args_val = evaluate(args, runtime_context)
		local returns_val = evaluate(returns, runtime_context)
		local resinfo_val = evaluate(resinfo, runtime_context)
		return value.host_function_type(args_val, returns_val, resinfo_val)
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
		local level, depth = typed_term:unwrap_star()
		return value.star(level, depth)
	elseif typed_term:is_prop() then
		local level = typed_term:unwrap_prop()
		return value.prop(level)
	elseif typed_term:is_host_tuple_type() then
		local desc = typed_term:unwrap_host_tuple_type()
		local desc_val = evaluate(desc, runtime_context)
		return value.host_tuple_type(desc_val)
	elseif typed_term:is_range() then
		local lower_bounds, upper_bounds, relation = typed_term:unwrap_range()
		local lower_acc, upper_acc = value_array(), value_array()

		for _, v in lower_bounds:ipairs() do
			lower_acc:append(evaluate(v, runtime_context))
		end

		for _, v in upper_bounds:ipairs() do
			upper_acc:append(evaluate(v, runtime_context))
		end

		local reln = evaluate(relation, runtime_context)

		return value.range(lower_acc, upper_acc, reln)
	elseif typed_term:is_singleton() then
		local supertype, val = typed_term:unwrap_singleton()
		local supertype_val = evaluate(supertype, runtime_context)
		return value.singleton(supertype_val, val)
	elseif typed_term:is_program_sequence() then
		local first, rest = typed_term:unwrap_program_sequence()
		local startprog = evaluate(first, runtime_context)
		if startprog:is_program_end() then
			local first_res = startprog:unwrap_program_end()
			return evaluate(rest, runtime_context:append(first_res))
		elseif startprog:is_program_cont() then
			local effect_id, effect_arg, cont = startprog:unwrap_program_cont()
			local restframe = terms.continuation.frame(runtime_context, rest)
			return value.program_cont(effect_id, effect_arg, terms.continuation.sequence(cont, restframe))
		else
			error(
				"unrecognized program variant: expected program_end or program_cont, got " .. startprog:pretty_print()
			)
		end
	elseif typed_term:is_program_end() then
		local result = typed_term:unwrap_program_end()

		return value.program_end(evaluate(result, runtime_context))
	elseif typed_term:is_program_invoke() then
		local effect_term, arg_term = typed_term:unwrap_program_invoke()
		local effect_val = evaluate(effect_term, runtime_context)
		local arg_val = evaluate(arg_term, runtime_context)
		if effect_val:is_effect_elem() then
			local effect_id = effect_val:unwrap_effect_elem()
			return value.program_cont(effect_id, arg_val, terms.continuation.empty)
		end
		error "NYI stuck program invoke"
	elseif typed_term:is_program_type() then
		local effect_type, result_type = typed_term:unwrap_program_type()
		local effect_type_val = evaluate(effect_type, runtime_context)
		local result_type_val = evaluate(result_type, runtime_context)
		return value.program_type(effect_type_val, result_type_val)
	elseif typed_term:is_srel_type() then
		local target = typed_term:unwrap_srel_type()
		return value.srel_type(evaluate(target, runtime_context))
	elseif typed_term:is_constrained_type() then
		local constraints = typed_term:unwrap_constrained_type()
		local mv = typechecker_state:metavariable(nil, false)
		for i, constraint in constraints:ipairs() do
			---@cast constraint constraintelem
			if constraint:is_sliced_constrain() then
				local rel, right, ctx, cause = constraint:unwrap_sliced_constrain()
				typechecker_state:send_constrain(nil, mv:as_value(), rel, ctx, evaluate(right, runtime_context), cause)
			elseif constraint:is_constrain_sliced() then
				local left, ctx, rel, cause = constraint:unwrap_constrain_sliced()
				typechecker_state:send_constrain(ctx, evaluate(left, runtime_context), rel, nil, mv:as_value(), cause)
			elseif constraint:is_sliced_leftcall() then
				local arg, rel, right, ctx, cause = constraint:unwrap_sliced_leftcall()
				typechecker_state:send_constrain(
					nil,
					apply_value(mv:as_value(), evaluate(arg, runtime_context)),
					rel,
					ctx,
					evaluate(right, runtime_context),
					cause
				)
			elseif constraint:is_leftcall_sliced() then
				local left, ctx, arg, rel, cause = constraint:unwrap_leftcall_sliced()
				typechecker_state:send_constrain(
					ctx,
					apply_value(evaluate(left, runtime_context), evaluate(arg, runtime_context)),
					rel,
					nil,
					mv:as_value(),
					cause
				)
			elseif constraint:is_sliced_rightcall() then
				local rel, right, ctx, arg, cause = constraint:unwrap_sliced_rightcall()
				typechecker_state:send_constrain(
					nil,
					mv:as_value(),
					rel,
					ctx,
					apply_value(evaluate(right, runtime_context), evaluate(arg, runtime_context)),
					cause
				)
			elseif constraint:is_rightcall_sliced() then
				local left, ctx, rel, arg, cause = constraint:unwrap_rightcall_sliced()
				typechecker_state:send_constrain(
					ctx,
					evaluate(left, runtime_context),
					rel,
					nil,
					apply_value(mv:as_value(), evaluate(arg, runtime_context)),
					cause
				)
			else
				error "unrecognized constraint kind"
			end
		end
		return mv:as_value()
	elseif typed_term:is_union_type() then
		local a, b = typed_term:unwrap_union_type()
		return value.union_type(evaluate(a, runtime_context), evaluate(b, runtime_context))
	elseif typed_term:is_intersection_type() then
		local a, b = typed_term:unwrap_intersection_type()
		return value.intersection_type(evaluate(a, runtime_context), evaluate(b, runtime_context))
	else
		error("evaluate: unknown kind: " .. typed_term.kind)
	end

	error("unreachable!?")
end

---@alias effect_handler fun(arg: value, cont: continuation): value
---@type {[thread] : {[table] : effect_handler } }
local thread_effect_handlers = setmetatable({}, { __mode = "k" })

---given an evaluated program value, execute it for effects
---@param prog value
---@return value
local function execute_program(prog)
	if prog:is_program_end() then
		return prog:unwrap_program_end()
	elseif prog:is_program_cont() then
		local effectid, effectarg, cont = prog:unwrap_program_cont()
		local thr = coroutine.running()
		local handler = thread_effect_handlers[thr][effectid]
		return handler(effectarg, cont)
	end
	error "unrecognized program variant"
end

---resume a program after an effect completes
---@param cont continuation
---@param arg value
local function invoke_continuation(cont, arg)
	if cont:is_empty() then
		return arg
	elseif cont:is_frame() then
		local ctx, term = cont:unwrap_frame()
		local frameres = evaluate(term, ctx:append(arg))
		return execute_program(frameres)
	elseif cont:is_sequence() then
		local first, rest = cont:unwrap_sequence()
		--TODO: refold continuations and make stack tracing alicorn nice
		local firstres = invoke_continuation(first, arg)
		return invoke_continuation(rest, firstres)
	end
end

---set an effect handler for a specified effect
---@param effect_id table
---@param handler effect_handler
---@return effect_handler
local function register_effect_handler(effect_id, handler)
	local thr = coroutine.running()
	local map = thread_effect_handlers[thr] or {}
	thread_effect_handlers[thr] = map
	local old = map[effect_id]
	map[effect_id] = handler
	return old
end

---@type effect_handler
local function host_effect_handler(arg, cont)
	---@type value, value
	local func, farg = arg:unwrap_tuple_value():unpack()
	if not func:is_host_value() or not farg:is_host_tuple_value() then
		error "host effect information is the wrong kind"
	end
	local res = value.host_tuple_value(host_array(func:unwrap_host_value()(farg:unwrap_host_tuple_value():unpack())))
	return invoke_continuation(cont, res)
end

register_effect_handler(terms.lua_prog, host_effect_handler)

---@class Variance
---@field positive boolean
---@field srel SubtypeRelation
local Variance = {}

---@type SubtypeRelation
UniverseOmegaRelation = setmetatable({
	debug_name = "UniverseOmegaRelation",
	Rel = luatovalue(function(a, b)
		error("nyi")
	end),
	refl = luatovalue(function(a)
		error("nyi")
	end),
	antisym = luatovalue(function(a, b, r1, r2)
		error("nyi")
	end),
	constrain = luatovalue(function(lctx, val, rctx, use)
		local ok, err = U.tag(
			"check_concrete",
			{ val = val, use = use, block_level = typechecker_state.block_level },
			check_concrete,
			lctx,
			val,
			rctx,
			use
		)
		if not ok then
			error(err)
		end
	end),
}, subtype_relation_mt)

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

local function IndexedCollection(indices)
	local res = { _collection = {}, _index_store = {} }
	function res:all()
		return self._collection
	end
	for k, v in pairs(indices) do
		res._index_store[k] = {}
		res[k] = function(self, ...)
			if rawget(self, "__lock") then
				error(
					"Modifying a shadowed object! This should never happen!\n"
						.. "@@@@@@@@@@@@@@@\n"
						.. "@@@ STACK 1 @@@\n"
						.. "@@@@@@@@@@@@@@@\n"
						.. rawget(self, "__locktrace")
						.. "\n@@@@@@@@@@@@@@@\n"
						.. "@@@ STACK 2 @@@\n"
						.. "@@@@@@@@@@@@@@@\n"
						.. "modify attempted here"
				)
			end
			local args = { ... }
			assert(#args == #v, "Must have one argument per key extractor")

			local store = self._index_store[k]
			for i = 1, #v do
				if store[args[i]] == nil then
					-- We early return here to make things easier, but if you require that all nodes have a persistent identity,
					-- you'll have to re-implement the behavior below where it inserts empty tables until the search query succeeds.
					return {}

					-- If you want to implement this behavior, then this function must also shadow the tree properly
					--store[args[i]] = {}
				end

				store = store[args[i]]
			end
			return store
		end
	end

	---This function is made easier because we know we're ALWAYS inserting a new item, so we ALWAYS shadow any tables we
	---encounter that aren't shadowed yet (and also aren't new insertions on this layer).
	---@generic T
	---@param obj any
	---@param store T
	---@param i integer
	---@param extractors any[]
	---@param level integer
	---@return T
	local function insert_tree(obj, store, i, extractors, level)
		if store == nil then
			store = {}
			level = -1
		end
		local curlevel = U.getshadowdepth(store)
		if i > #extractors then
			if level > 0 then
				for j = curlevel + 1, level do
					store = U.shadowarray(store)
				end
				assert(U.getshadowdepth(store) == level, "Improper shadowing happened!")
			end
			U.append(store, obj)
			return store
		end
		local kx = extractors[i]
		local key = kx(obj)
		if level > 0 then
			-- shadow the node enough times so that the levels match
			for j = curlevel + 1, level do
				store = U.shadowtable(store)
			end
			assert(U.getshadowdepth(store) == level, "Improper shadowing happened!")
		end
		-- Note: it might be *slightly* more efficient to only reassign if the returned table is different, but the commit
		-- only copies completely new keys anyway so it doesn't really matter.
		local oldlevel = 0
		if store[key] then
			oldlevel = U.getshadowdepth(store[key])
		end
		store[key] = insert_tree(obj, store[key], i + 1, extractors, level)

		-- Any time we shadow something more than once, we have some "skipped" levels in-between that must be assigned
		local parent = store
		local child = store[key]
		local newlevel = U.getshadowdepth(child)
		for j = oldlevel + 1, newlevel - 1 do
			parent = rawget(parent, "__shadow")
			child = rawget(child, "__shadow")
			rawset(parent, key, child)
		end

		return store
	end

	function res:add(obj)
		if rawget(self, "__lock") then
			error("Modifying a shadowed object! This should never happen!")
		end
		U.append(self._collection, obj)
		for name, extractors in pairs(indices) do
			self._index_store[name] =
				insert_tree(obj, self._index_store[name], 1, extractors, U.getshadowdepth(self._index_store))
		end
	end

	local function store_copy_inner(n, store)
		local copy = {}
		if n == 0 then
			for i, v in ipairs(store) do
				copy[i] = v
			end
			return copy
		else
			for k, v in pairs(store) do
				copy[k] = store_copy_inner(n - 1, v)
			end
			return copy
		end
	end

	local function store_copy(store)
		local copy = {}
		for name, extractors in pairs(indices) do
			local depth = #extractors
			copy[name] = store_copy_inner(depth, store[name])
		end
		return copy
	end

	function res:shadow()
		local n = U.shallow_copy(self) -- Copy all the functions into a new table
		n._collection = U.shadowarray(self._collection) -- Shadow collection
		n._index_store = U.shadowtable(self._index_store)
		rawset(self, "__lock", true) --  This has to be down here or we'll accidentally copy it
		rawset(self, "__locktrace", metalanguage.stack_trace("shadow occurred here"))
		rawset(n, "__shadow", self)
		return n
	end

	---To commit all the tree nodes, we only copy keys that do not exist at all in the shadowed table
	---@param n table
	local function commit_tree_node(n)
		setmetatable(n, nil)
		assert(type(n) == "table")
		local base = rawget(n, "__shadow")
		if base then
			for k, v in pairs(n) do
				-- skip internal keys
				if type(k) == "string" and string.sub(k, 1, 2) == "__" then
					goto continue
				end
				if base[k] == nil then
					rawset(base, k, v)
				end
				-- The base of the tree is actually an array, so we don't recurse into it
				if type(k) ~= "integer" then
					commit_tree_node(v)
				end
				::continue::
			end
			rawset(n, "__shadow", nil)
			rawset(base, "__lock", nil)
		end
	end

	local function revert_tree_node(n)
		setmetatable(n, nil)
		assert(type(n) == "table")
		local base = rawget(n, "__shadow")
		if base then
			rawset(n, "__shadow", nil)
			rawset(base, "__lock", nil)
			rawset(base, "__locktrace", nil)
		end
	end

	function res:commit()
		U.commit(self._collection)

		commit_tree_node(self._index_store)
		local orig = rawget(self, "__shadow")
		rawset(orig, "__lock", nil)
		rawset(orig, "__locktrace", nil)
		rawset(self, "__shadow", nil)
	end

	function res:revert()
		U.revert(self._collection)

		revert_tree_node(self._index_store)
		local orig = rawget(self, "__shadow")
		rawset(orig, "__lock", nil)
		rawset(orig, "__locktrace", nil)
		rawset(self, "__shadow", nil)
	end

	return res
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

function TraitRegistry:revert()
	U.revert(self.traits)
end

trait_registry_mt = { __index = TraitRegistry }

local function trait_registry()
	return setmetatable({ traits = {} }, trait_registry_mt)
end
---@class TypeCheckerState
---@field pending ReachabilityQueue
---@field graph Reachability
---@field values [value, TypeCheckerTag, TypecheckingContext|nil][]
---@field block_level integer
---@field valcheck { [value]: integer }
---@field usecheck { [value]: integer }
---@field trait_registry TraitRegistry
local TypeCheckerState = {}
--@field values { val: value, tag: TypeCheckerTag, context: TypecheckingContext|nil }

---@alias NodeID integer the ID of a node in the graph

---@module "evaluator.edge"
local CEdge = gen.declare_type()

-- stylua: ignore
CEdge:define_enum("edge", {
	{ "ConstrainEdge", {
		"left",  gen.builtin_number,
		"rel",  SubtypeRelation,
		"shallowest_block", gen.builtin_number,
		"right", gen.builtin_number,
	} },
	{ "LeftCallEdge", {
		"left",  gen.builtin_number,
		"arg",  value,
		"rel",  SubtypeRelation,
		"shallowest_block", gen.builtin_number,
		"right", gen.builtin_number,
	} },
	{ "RightCallEdge", {
		"left",  gen.builtin_number,
		"rel",  SubtypeRelation,
		"shallowest_block", gen.builtin_number,
		"right", gen.builtin_number,
		"arg",  value,
	} },
}
)

---@class ConstrainEdge
---@field left NodeID
---@field rel SubtypeRelation
---@field shallowest_block integer
---@field right NodeID

---@class LeftCallEdge
---@field left NodeID
---@field arg value
---@field rel SubtypeRelation
---@field shallowest_block integer
---@field right NodeID

---@class RightCallEdge
---@field left NodeID
---@field rel SubtypeRelation
---@field shallowest_block integer
---@field right NodeID
---@field arg value

-- I wish I had generics in LuaCATS

---@class ConstrainCollection
---@field add fun(self: ConstrainCollection,edge: ConstrainEdge)
---@field all fun(self: ConstrainCollection): ConstrainEdge[]
---@field from fun(self: ConstrainCollection,left: NodeID): ConstrainEdge[]
---@field to fun(self: ConstrainCollection,right: NodeID): ConstrainEdge[]
---@field between fun(self: ConstrainCollection,left: NodeID, right: NodeID): ConstrainEdge[]
---@field shadow fun(self: ConstrainCollection) : ConstrainCollection
---@field commit fun(self: ConstrainCollection)
---@field revert fun(self: ConstrainCollection)

---@class LeftCallCollection
---@field add fun(self: LeftCallCollection,edge: LeftCallEdge)
---@field all fun(self: LeftCallCollection): LeftCallEdge[]
---@field from fun(self: LeftCallCollection,left: NodeID): LeftCallEdge[]
---@field to fun(self: LeftCallCollection,right: NodeID): LeftCallEdge[]
---@field between fun(self: LeftCallCollection,left: NodeID, right: NodeID): LeftCallEdge[]
---@field shadow fun(self: LeftCallCollection) : LeftCallCollection
---@field commit fun(self: LeftCallCollection)
---@field revert fun(self: LeftCallCollection)

---@class RightCallCollection
---@field add fun(self: RightCallCollection,edge: RightCallEdge)
---@field all fun(self: RightCallCollection): RightCallEdge[]
---@field from fun(self: RightCallCollection,left: NodeID): RightCallEdge[]
---@field to fun(self: RightCallCollection,right: NodeID): RightCallEdge[]
---@field between fun(self: RightCallCollection,left: NodeID, right: NodeID): RightCallEdge[]
---@field shadow fun(self: RightCallCollection) : RightCallCollection
---@field commit fun(self: RightCallCollection)
---@field revert fun(self: RightCallCollection)

---@class Reachability
---@field constrain_edges ConstrainCollection
---@field leftcall_edges LeftCallCollection
---@field rightcall_edges RightCallCollection
---@field nodecount integer
local Reachability = {}
local reachability_mt

---This shadowing works a bit differently because it overrides setinsert to be shadow-aware
---@return Reachability
function Reachability:shadow()
	return setmetatable({
		constrain_edges = self.constrain_edges:shadow(),
		leftcall_edges = self.leftcall_edges:shadow(),
		rightcall_edges = self.rightcall_edges:shadow(),
	}, reachability_mt)
end

function Reachability:commit()
	self.constrain_edges:commit()
	self.leftcall_edges:commit()
	self.rightcall_edges:commit()
end

function Reachability:revert()
	self.constrain_edges:revert()
	self.leftcall_edges:revert()
	self.rightcall_edges:revert()
end

---@alias ReachabilityQueue edgenotif[]

---check for combinations of constrain edges that induce new constraints in response to a constrain edges
---@param edge ConstrainEdge
---@param queue ReachabilityQueue
---@param cause any
function Reachability:constrain_transitivity(edge, queue, cause)
	for _, l2 in ipairs(self.constrain_edges:to(edge.left)) do
		---@cast l2 ConstrainEdge
		if l2.rel ~= edge.rel then
			error("Relations do not match! " .. l2.rel.debug_name .. " is not " .. edge.rel.debug_name)
		end
		U.append(
			queue,
			EdgeNotif.Constrain(
				l2.left,
				edge.rel,
				edge.right,
				math.min(edge.shallowest_block, l2.shallowest_block),
				cause
			)
		)
	end
	for _, r2 in ipairs(self.constrain_edges:from(edge.right)) do
		---@cast r2 ConstrainEdge
		if r2.rel ~= edge.rel then
			error("Relations do not match! " .. r2.rel.debug_name .. " is not " .. edge.rel.debug_name)
		end
		U.append(
			queue,
			EdgeNotif.Constrain(
				edge.left,
				edge.rel,
				r2.right,
				math.min(edge.shallowest_block, r2.shallowest_block),
				cause
			)
		)
	end
end

---@param left integer
---@param right integer
---@param rel SubtypeRelation
---@param shallowest_block integer
---@return boolean
function Reachability:add_constrain_edge(left, right, rel, shallowest_block)
	assert(type(left) == "number", "left isn't an integer!")
	assert(type(right) == "number", "right isn't an integer!")

	for _, edge in ipairs(self.constrain_edges:between(left, right)) do
		if edge.rel ~= rel then
			error(
				"edges are not unique and have mismatched constraints: "
					.. tostring(edge.rel.debug_name)
					.. " ~= "
					.. tostring(rel.debug_name)
			)
			--TODO: maybe allow between concrete heads
		end
		return false
	end

	---@type ConstrainEdge
	local edge = { left = left, right = right, rel = rel, shallowest_block = shallowest_block }

	self.constrain_edges:add(edge)

	return true
end

---@param left integer
---@param arg value
---@param rel SubtypeRelation
---@param right integer
---@param shallowest_block integer
---@return boolean
function Reachability:add_call_left_edge(left, arg, rel, right, shallowest_block)
	assert(type(left) == "number", "left isn't an integer!")
	assert(type(right) == "number", "right isn't an integer!")

	for _, edge in ipairs(self.leftcall_edges:between(left, right)) do
		if rel == edge.rel and arg == edge.arg then
			return false
		end
	end
	---@type LeftCallEdge
	local edge = {
		left = left,
		arg = arg,
		rel = rel,
		right = right,
		shallowest_block = shallowest_block,
	}

	self.leftcall_edges:add(edge)

	return true
end

---@param left integer
---@param rel SubtypeRelation
---@param right integer
---@param arg value
---@param shallowest_block integer
---@return boolean
function Reachability:add_call_right_edge(left, rel, right, arg, shallowest_block)
	assert(type(left) == "number", "left isn't an integer!")
	assert(type(right) == "number", "right isn't an integer!")

	for _, edge in ipairs(self.rightcall_edges:between(left, right)) do
		if rel == edge.rel and arg == edge.arg then
			return false
		end
	end
	---@type RightCallEdge
	local edge = {
		left = left,
		arg = arg,
		rel = rel,
		right = right,
		shallowest_block = shallowest_block,
	}

	self.rightcall_edges:add(edge)
	return true
end

reachability_mt = { __index = Reachability }

---@return Reachability
local function reachability()
	return setmetatable({
		constrain_edges = IndexedCollection {
			from = {

				---@return integer
				---@param obj ConstrainEdge
				function(obj)
					return obj.left
				end,
			},
			to = {
				---@return integer
				---@param obj ConstrainEdge
				function(obj)
					return obj.right
				end,
			},
			between = {
				---@return integer
				---@param obj ConstrainEdge
				function(obj)
					return obj.left
				end,
				---@return integer
				---@param obj ConstrainEdge
				function(obj)
					return obj.right
				end,
			},
		},
		leftcall_edges = IndexedCollection {
			from = {
				---@return integer
				---@param obj LeftCallEdge
				function(obj)
					return obj.left
				end,
			},
			to = {
				---@return integer
				---@param obj LeftCallEdge
				function(obj)
					return obj.right
				end,
			},
			between = {
				---@return integer
				---@param obj LeftCallEdge
				function(obj)
					return obj.left
				end,
				---@return integer
				---@param obj LeftCallEdge
				function(obj)
					return obj.right
				end,
			},
		},
		rightcall_edges = IndexedCollection {
			from = {
				---@return integer
				---@param obj RightCallEdge
				function(obj)
					return obj.left
				end,
			},
			to = {
				---@return integer
				---@param obj RightCallEdge
				function(obj)
					return obj.right
				end,
			},
			between = {
				---@return integer
				---@param obj RightCallEdge
				function(obj)
					return obj.left
				end,
				---@return integer
				---@param obj RightCallEdge
				function(obj)
					return obj.right
				end,
			},
		},
	}, reachability_mt)
end

---@enum TypeCheckerTag
local TypeCheckerTag = {
	VALUE = { VALUE = "VALUE" },
	USAGE = { USAGE = "USAGE" },
	METAVAR = { METAVAR = "METAVAR" },
	RANGE = { RANGE = "RANGE" },
}
---@param lctx TypecheckingContext
---@param val value
---@param use value
---@param rctx TypecheckingContext
---@param cause any
function TypeCheckerState:queue_subtype(lctx, val, rctx, use, cause)
	local l = U.tag("check_value", { val = val, use = use }, self.check_value, self, val, TypeCheckerTag.VALUE, lctx)
	local r = U.tag("check_value", { val = val, use = use }, self.check_value, self, use, TypeCheckerTag.USAGE, rctx)
	assert(type(l) == "number", "l isn't number, instead found " .. tostring(l))
	assert(type(r) == "number", "r isn't number, instead found " .. tostring(r))
	U.append(self.pending, EdgeNotif.Constrain(l, UniverseOmegaRelation, r, self.block_level, cause))
end

---@param lctx TypecheckingContext
---@param val value
---@param rel SubtypeRelation
---@param rctx TypecheckingContext
---@param use value
---@param cause any
function TypeCheckerState:queue_constrain(lctx, val, rel, rctx, use, cause)
	local l = U.tag("check_value", { val = val, use = use }, self.check_value, self, val, TypeCheckerTag.VALUE, lctx)
	local r = U.tag("check_value", { val = val, use = use }, self.check_value, self, use, TypeCheckerTag.USAGE, rctx)
	assert(type(l) == "number", "l isn't number, instead found " .. tostring(l))
	assert(type(r) == "number", "r isn't number, instead found " .. tostring(r))
	U.append(self.pending, EdgeNotif.Constrain(l, rel, r, self.block_level, cause))
end

---@param lctx TypecheckingContext
---@param val value
---@param rel SubtypeRelation
---@param rctx TypecheckingContext
---@param use value
---@param cause any
function TypeCheckerState:send_constrain(lctx, val, rel, rctx, use, cause)
	if #self.pending == 0 then
		self:constrain(val, lctx, use, rctx, rel, cause)
	else
		self:queue_constrain(lctx, val, rel, rctx, use, cause)
	end
end

---@param v value
---@param tag TypeCheckerTag
---@param context TypecheckingContext
---@return NodeID
function TypeCheckerState:check_value(v, tag, context)
	assert(v, "nil passed into check_value!")

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

	local checker = self.valcheck
	if tag == TypeCheckerTag.USAGE then
		checker = self.usecheck
	end

	if checker[v] then
		return checker[v]
	end

	if v:is_range() then
		U.append(self.values, { v, TypeCheckerTag.RANGE, context })
		self.valcheck[v] = #self.values
		self.usecheck[v] = #self.values
		local v_id = #self.values

		local lower_bounds, upper_bounds, relation = v:unwrap_range()

		for _, bound in ipairs(lower_bounds) do
			self:queue_constrain(context, bound, relation:unwrap_host_value(), context, v, "range unpacking")
		end

		for _, bound in ipairs(upper_bounds) do
			self:queue_constrain(context, v, relation:unwrap_host_value(), context, bound, "range_unpacking")
		end

		return v_id
	else
		U.append(self.values, { v, tag, context })
		checker[v] = #self.values
		return #self.values
	end
end

---@return Metavariable
---@param context TypecheckingContext
---@param trait boolean?
function TypeCheckerState:metavariable(context, trait)
	local i = #self.values + 1
	local mv = setmetatable(
		-- block level here should probably be inside the context and not inside the metavariable
		{ value = i, usage = i, trait = trait or false, block_level = self.block_level },
		terms.metavariable_mt
	)
	U.append(self.values, { mv:as_value(), TypeCheckerTag.METAVAR })
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
		if lvalue:is_neutral() and lvalue:unwrap_neutral():is_application_stuck() then
			return
		end
		if rvalue:is_neutral() and rvalue:unwrap_neutral():is_application_stuck() then
			return
		end
		-- Unpacking tuples hasn't been fixed in VSCode yet (despite the issue being closed???) so we have to override the types: https://github.com/LuaLS/lua-language-server/issues/1816
		local tuple_params = value_array(
			value.host_value(lctx),
			value.host_value(lvalue),
			value.host_value(rctx),
			value.host_value(rvalue)
		)
		-- TODO: how do we pass in the type contexts???
		U.tag(
			"apply_value",
			{ lvalue = lvalue, rvalue = rvalue, block_level = typechecker_state.block_level, rel = rel.debug_name },
			apply_value,
			rel.constrain,
			value.tuple_value(tuple_params)
		)
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

	if --[[ltag == TypeCheckerTag.METAVAR and]]
		lvalue:is_neutral() and lvalue:unwrap_neutral():is_application_stuck()
	then
		local f, arg = lvalue:unwrap_neutral():unwrap_application_stuck()
		local l = self:check_value(value.neutral(f), TypeCheckerTag.VALUE, nil)
		U.append(
			self.pending,
			EdgeNotif.CallLeft(l, arg, rel, right, self.block_level, "Inside constrain_induce_call ltag")
		)
	end

	if --[[rtag == TypeCheckerTag.METAVAR and]]
		rvalue:is_neutral() and rvalue:unwrap_neutral():is_application_stuck()
	then
		local f, arg = rvalue:unwrap_neutral():unwrap_application_stuck()
		local r = self:check_value(value.neutral(f), TypeCheckerTag.USAGE, nil)
		U.append(
			self.pending,
			EdgeNotif.CallRight(left, rel, r, arg, self.block_level, "Inside constrain_induce_call rtag")
		)
	end
end

---check for compositions of a constrain edge and a left call edge in response to a new constrain edge
---@param edge ConstrainEdge
function TypeCheckerState:constrain_leftcall_compose_1(edge)
	local mvalue, mtag, mctx = table.unpack(self.values[edge.right])
	if mtag == TypeCheckerTag.METAVAR then
		for _, r2 in ipairs(self.graph.leftcall_edges:from(edge.right)) do
			if FunctionRelation(r2.rel) ~= edge.rel then
				error(
					"Relations do not match! " .. tostring(FunctionRelation(r2.rel)) .. " is not " .. tostring(edge.rel)
				)
			end
			U.append(
				self.pending,
				EdgeNotif.CallLeft(
					edge.left,
					r2.arg,
					r2.rel,
					r2.right,
					math.min(edge.shallowest_block, r2.shallowest_block) "constrain leftcall composition induced by constrain"
				)
			)
		end
	end
end

---check for compositions of a constrain edge and a left call edge in response to a new left call edge
---@param edge LeftCallEdge
function TypeCheckerState:constrain_leftcall_compose_2(edge)
	local mvalue, mtag, mctx = table.unpack(self.values[edge.left])
	if mtag == TypeCheckerTag.METAVAR then
		for _, l2 in ipairs(self.graph.constrain_edges:to(edge.left)) do
			if l2.rel ~= FunctionRelation(edge.rel) then
				error(
					"Relations do not match! " .. tostring(l2.rel) .. " is not " .. tostring(FunctionRelation(edge.rel))
				)
			end
			U.append(
				self.pending,
				EdgeNotif.CallLeft(
					edge.left,
					edge.arg,
					edge.rel,
					l2.right,
					math.min(edge.shallowest_block, l2.shallowest_block),
					"constrain leftcall composition induced by leftcall"
				)
			)
		end
	end
end

---check for compositions of a right call edge and a constrain edge in response to a new constrain edge
---@param edge ConstrainEdge
function TypeCheckerState:rightcall_constrain_compose_2(edge)
	local mvalue, mtag, mctx = table.unpack(self.values[edge.left])
	if mtag == TypeCheckerTag.METAVAR then
		for _, l2 in ipairs(self.graph.rightcall_edges:to(edge.left)) do
			if FunctionRelation(l2.rel) ~= edge.rel then
				error(
					"Relations do not match! " .. tostring(FunctionRelation(l2.rel)) .. " is not " .. tostring(edge.rel)
				)
			end
			U.append(
				self.pending,
				EdgeNotif.CallRight(
					edge.left,
					l2.rel,
					l2.right,
					l2.arg,
					math.min(edge.shallowest_block, l2.shallowest_block),
					"rightcall constrain composition induced by constrain"
				)
			)
		end
	end
end

---check for compositions of a right call edge and a constrain edge in response to a new right call edge
---@param edge RightCallEdge
function TypeCheckerState:rightcall_constrain_compose_1(edge)
	local mvalue, mtag, mctx = table.unpack(self.values[edge.right])
	if mtag == TypeCheckerTag.METAVAR then
		for _, r2 in ipairs(self.graph.constrain_edges:from(edge.right)) do
			if r2.rel ~= FunctionRelation(edge.rel) then
				error(
					"Relations do not match! " .. tostring(r2.rel) .. " is not " .. tostring(FunctionRelation(edge.rel))
				)
			end
			U.append(
				self.pending,
				EdgeNotif.CallRight(
					edge.left,
					edge.rel,
					r2.right,
					edge.arg,
					math.min(edge.shallowest_block, r2.shallowest_block),
					"constrain leftcall composition induced by leftcall"
				)
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
	self:queue_constrain(val_context, val, rel, use_context, use, cause)

	while #self.pending > 0 do
		local item = U.pop(self.pending)

		if item:is_Constrain() then
			local left, rel, right, shallowest_block, cause = item:unwrap_Constrain()

			if self.graph:add_constrain_edge(left, right, rel, self.block_level) then
				---@type ConstrainEdge
				local edge = { left = left, rel = rel, right = right, shallowest_block = self.block_level }
				self.graph:constrain_transitivity(edge, self.pending, cause)
				U.tag(
					"check_heads",
					{ left = left, right = right, rel = rel.debug_name },
					self.check_heads,
					self,
					left,
					right,
					rel
				)
				self:constrain_induce_call(left, right, rel)
				self:constrain_leftcall_compose_1(edge)
				self:rightcall_constrain_compose_2(edge)
			end
		elseif item:is_CallLeft() then
			local left, arg, rel, right, shallowest_block, cause = item:unwrap_CallLeft()

			if self.graph:add_call_left_edge(left, arg, rel, right, self.block_level) then
				---@type LeftCallEdge
				local edge = { left = left, arg = arg, rel = rel, right = right, shallowest_block = self.block_level }
				self:constrain_leftcall_compose_2(edge)
			end
		elseif item:is_CallRight() then
			local left, rel, right, arg, shallowest_block, cause = item:unwrap_CallRight()

			if self.graph:add_call_right_edge(left, rel, right, arg, self.block_level) then
				---@type RightCallEdge
				local edge = { left = left, rel = rel, right = right, arg = arg, shallowest_block = self.block_level }
				self:rightcall_constrain_compose_1(edge)
			end
		else
			error("Unknown edge kind!")
		end
	end

	assert(#self.pending == 0, "pending was not drained!")
	return true
end

---extract a region of a graph based on the block depth around a metavariable, for use in substitution
---@param mv Metavariable
---@param mappings {[integer]: typed} the placeholder we are trying to get rid of by substituting
---@param context_len integer number of bindings in the runtime context already used - needed for closures
---@return typed
function TypeCheckerState:slice_constraints_for(mv, mappings, context_len)
	-- take only the constraints that are against this metavariable in such a way that it remains valid as we exit the block
	-- if the metavariable came from a "lower" block it is still in scope and may gain additional constraints in the future
	-- because this metavariable is from an outer scope, it doesn't have any constraints against something that is in the deeper scope and needs to be substituted,
	-- so we want to NOT include anything on the deeper side of a constraint towards this metavariable

	-- left is tail, right is head
	-- things flow ltr
	-- values flow to usages

	local constraints = array(terms.constraintelem)()

	local function getnode(id)
		return self.values[id][1]
	end
	local function getctx(id)
		return self.values[id][3] or terms.typechecking_context() --FIXME
	end
	local function slice_edgeset(edgeset, extractor, callback)
		for _, edge in ipairs(edgeset) do
			if self.values[extractor(edge)][2] == TypeCheckerTag.METAVAR then
				local mvo = self.values[extractor(edge)][1]

				if
					mvo:is_neutral()
					and mvo:unwrap_neutral():is_free()
					and mvo:unwrap_neutral():unwrap_free():is_metavariable()
				then
					local mvo_inner = mvo:unwrap_neutral():unwrap_free():unwrap_metavariable()
					if mvo_inner.block_level < self.block_level then
						callback(edge)
					end
				else
					error "incorrectly labelled as a metavariable"
				end
			else
				if not (self.values[extractor(edge)][2] == TypeCheckerTag.RANGE) then
					callback(edge)
				end
			end
		end
	end

	slice_edgeset(self.graph.constrain_edges:to(mv.usage), function(edge)
		return edge.left
	end, function(edge)
		constraints:append(
			terms.constraintelem.constrain_sliced(
				substitute_inner(getnode(edge.left), mappings, context_len),
				getctx(edge.left),
				edge.rel,
				edge.cause
			)
		)
	end)
	slice_edgeset(self.graph.constrain_edges:from(mv.usage), function(edge)
		return edge.right
	end, function(edge)
		constraints:append(
			terms.constraintelem.sliced_constrain(
				edge.rel,
				substitute_inner(getnode(edge.right), mappings, context_len),
				getctx(edge.right),
				edge.cause
			)
		)
	end)
	slice_edgeset(self.graph.leftcall_edges:to(mv.usage), function(edge)
		return edge.left
	end, function(edge)
		constraints:append(
			terms.constraintelem.leftcall_sliced(
				substitute_inner(getnode(edge.left), mappings, context_len),
				getctx(edge.left),
				substitute_inner(edge.arg, mappings, context_len),
				edge.rel,
				edge.cause
			)
		)
	end)
	slice_edgeset(self.graph.leftcall_edges:from(mv.usage), function(edge)
		return edge.right
	end, function(edge)
		constraints:append(
			terms.constraintelem.sliced_leftcall(
				substitute_inner(edge.arg, mappings, context_len),
				edge.rel,
				substitute_inner(getnode(edge.right), mappings, context_len),
				getctx(edge.right),
				edge.cause
			)
		)
	end)
	slice_edgeset(self.graph.rightcall_edges:to(mv.usage), function(edge)
		return edge.left
	end, function(edge)
		constraints:append(
			terms.constraintelem.rightcall_sliced(
				substitute_inner(getnode(edge.left), mappings, context_len),
				getctx(edge.left),
				edge.rel,
				substitute_inner(edge.arg, mappings, context_len),
				edge.cause
			)
		)
	end)
	slice_edgeset(self.graph.rightcall_edges:from(mv.usage), function(edge)
		return edge.right
	end, function(edge)
		constraints:append(
			terms.constraintelem.sliced_rightcall(
				edge.rel,
				substitute_inner(getnode(edge.right), mappings, context_len),
				getctx(edge.right),
				substitute_inner(edge.arg, mappings, context_len),
				edge.cause
			)
		)
	end)

	return typed.constrained_type(constraints)
end

local typechecker_state_mt = { __index = TypeCheckerState }

---@return TypeCheckerState
function TypeCheckerState:shadow()
	return setmetatable({
		pending = U.shadowarray(self.pending),
		graph = self.graph:shadow(),
		block_level = self.block_level,
		values = U.shadowarray(self.values),
		valcheck = U.shadowtable(self.valcheck),
		usecheck = U.shadowtable(self.usecheck),
		trait_registry = self.trait_registry:shadow(),
		__shadow = self,
	}, typechecker_state_mt)
end

function TypeCheckerState:commit()
	U.commit(self.pending)
	self.graph:commit()
	self.__shadow.block_level = self.block_level
	U.commit(self.values)
	U.commit(self.valcheck)
	U.commit(self.usecheck)
	self.trait_registry:commit()
	rawset(self, "__shadow", nil)
end

function TypeCheckerState:revert()
	U.revert(self.pending)
	self.graph:revert()
	U.revert(self.values)
	U.revert(self.valcheck)
	U.revert(self.usecheck)
	self.trait_registry:revert()
	rawset(self, "__shadow", nil)
end

function TypeCheckerState:enter_block()
	self.block_level = self.block_level + 1
end
function TypeCheckerState:exit_block()
	self.block_level = self.block_level - 1
end

---@return TypeCheckerState
local function new_typechecker_state()
	return setmetatable({
		pending = {},
		graph = reachability(),
		values = {},
		block_level = 0,
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

	execute_program = execute_program,
	invoke_continuation = invoke_continuation,
	host_effect_handler = host_effect_handler,
	register_effect_handler = register_effect_handler,

	UniverseOmegaRelation = UniverseOmegaRelation,
	FunctionRelation = FunctionRelation,
	IndepTupleRelation = IndepTupleRelation,
	TupleDescRelation = TupleDescRelation,
	register_host_srel = register_host_srel,
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
		else
			typechecker_state:revert()
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
