local terms = require "./terms"
local runtime_context = terms.runtime_context
local typechecking_context = terms.typechecking_context
local checkable_term = terms.checkable_term
local inferrable_term = terms.inferrable_term
local typed_term = terms.typed_term
local free = terms.free
local quantity = terms.quantity
local visibility = terms.visibility
local purity = terms.purity
local result_info = terms.result_info
local value = terms.value
local neutral_value = terms.neutral_value
local prim_syntax_type = terms.prim_syntax_type
local prim_environment_type = terms.prim_environment_type
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

--DEBUG
do
	local qtype = terms.value.qtype
	terms.value.qtype = function(q, v)
		if v.kind == "value_qtype" then
			error "qtype in qtype"
		end
		return qtype(q, v)
	end
end

local function qtype(q, val)
	return value.qtype(value.quantity(q), val)
end
local function unrestricted(val)
	return qtype(quantity.unrestricted, val)
end
local function unrestricted_typed(term)
	return typed_term.qtype(typed_term.literal(value.quantity(quantity.unrestricted)), term)
end
local function linear(val)
	return qtype(quantity.linear, val)
end
local function erased(val)
	return qtype(quantity.erased, val)
end
local param_info_explicit = value.param_info(value.visibility(visibility.explicit))
local param_info_implicit = value.param_info(value.visibility(visibility.implicit))
local result_info_pure = value.result_info(result_info(purity.pure))
local result_info_effectful = value.result_info(result_info(purity.effectful))
local function tup_val(...)
	return value.tuple_value(value_array(...))
end
local function prim_tup_val(...)
	return value.prim_tuple_value(primitive_array(...))
end

local derivers = require "./derivers"
local traits = require "./traits"

local evaluate, infer, fitsinto, check, apply_value

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

local function const_combinator(v)
	return value.closure(typed_term.bound_variable(1), runtime_context():append(v))
end

local function get_level(t)
	-- TODO: this
	-- TODO: typecheck
	return 0
end

---@param val any an alicorn value
---@param mappings table the placeholder we are trying to get rid of by substituting
---@param context_len integer number of bindings in the runtime context already used - needed for closures
---@return unknown a typed term
local function substitute_inner(val, mappings, context_len)
	if val:is_quantity_type() then
		return typed_term.literal(val)
	elseif val:is_quantity() then
		return typed_term.literal(val)
	elseif val:is_visibility_type() then
		return typed_term.literal(val)
	elseif val:is_visibility() then
		return typed_term.literal(val)
	elseif val:is_qtype_type() then
		return typed_term.literal(val)
	elseif val:is_qtype() then
		local quantity, type = val:unwrap_qtype()
		quantity = typed_term.literal(quantity)
		type = substitute_inner(type, mappings, context_len)
		return typed_term.qtype(quantity, type)
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
		param_type = substitute_inner(param_type, mappings, context_len)
		param_info = substitute_inner(param_info, mappings, context_len)
		result_type = substitute_inner(result_type, mappings, context_len)
		result_info = substitute_inner(result_info, mappings, context_len)
		return typed_term.pi(param_type, param_info, result_type, result_info)
	elseif val:is_closure() then
		local ctxt = val.capture
		--FIXME: I am broken if the closure depends on its argument and isn't a constant closure
		local unique = free.unique({})
		local arg = value.neutral(neutral_value.free(unique))
		val = apply_value(val, arg)
		print("applied closure during substitution", val)
		-- Here we need to add the new arg placeholder to a map of things to substitute
		mappings[unique] = typed_term.bound_variable(context_len + 1)
		val = substitute_inner(val, mappings, context_len + 1)

		-- FIXME: this results in more captures every time we substitute a closure ->
		--   can cause non-obvious memory leaks
		--   since we don't yet remove unused captures from closure value
		return typed_term.lambda(val)
	elseif val:is_name_type() then
		return typed_term.literal(val)
	elseif val:is_name() then
		return typed_term.literal(val)
	elseif val:is_operative_value() then
		local userdata = val:unwrap_operative_value()
		userdata = substitute_inner(userdata, mappings, context_len)
		return typed_term.operative_cons(userdata)
	elseif val:is_operative_type() then
		local handler, userdata_type = val:unwrap_operative_type()
		handler = substitute_inner(handler, mappings, context_len)
		userdata_type = substitute_inner(userdata_type, mappings, context_len)
		return typed_term.operative_type_cons(handler, userdata_type)
	elseif val:is_tuple_value() then
		local elems = val:unwrap_tuple_value()
		local res = typed_array()
		for i, v in ipairs(elems) do
			res:append(substitute_inner(v, mappings, context_len))
		end
		return typed_term.tuple_cons(res)
	elseif val:is_tuple_type() then
		local decls = val:unwrap_tuple_type()
		decls = substitute_inner(decls, mappings, context_len)
		return typed_term.tuple_type(decls)
	elseif val:is_tuple_defn_type() then
		return typed_term.literal(val)
	elseif val:is_enum_value() then
		local constructor, arg = val:unwrap_enum_value()
		arg = substitute_inner(arg, mappings, context_len)
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

		if nval:is_prim_unbox_stuck() then
			local boxed = nval:unwrap_prim_unbox_stuck()
			return typed_term.prim_unbox(substitute_inner(value.neutral(boxed), mappings, context_len))
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
		param_type = substitute_inner(param_type, mappings, context_len)
		result_type = substitute_inner(result_type, mappings, context_len)
		return typed_term.prim_function_type(param_type, result_type)
	elseif val:is_prim_boxed_type() then
		local type = val:unwrap_prim_boxed_type()
		type = substitute_inner(type, mappings, context_len)
		return typed_term.prim_boxed_type(type)
	elseif val:is_prim_box_stuck() then
		error("not yet implemented")
	elseif val:is_prim_unbox_stuck() then
		error("not yet implemented")
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
		decls = substitute_inner(decls, mappings, context_len)
		return typed_term.prim_tuple_type(decls)
	else
		error("Unhandled value kind in substitute_inner: " .. val.kind)
	end
end

--for substituting a single var at index
local function substitute_type_variables(val, index)
	print("value before substituting (val)", val)
	local substituted = substitute_inner(val, {
		[index] = typed_term.bound_variable(1),
	}, 1)
	print("typed term after substitution (substituted)", substituted)
	return value.closure(substituted, runtime_context())
end

local function is_type_of_types(val)
	if not val:is_qtype() then
		error "val expected to be a qtype but wasn't"
	end
	local quantity, type = val:unwrap_qtype()
	return type:is_qtype_type() or type:is_star() or type:is_prop() or type:is_prim_type_type()
end

local make_inner_context
local infer_tuple_type, infer_tuple_type_unwrapped
local terms = require "./terms"
local value = terms.value

local fitsinto, fitsinto_qless
-- indexed by kind x kind
local fitsinto_comparers = {}

local function add_comparer(ka, kb, comparer)
	fitsinto_comparers[ka] = fitsinto_comparers[ka] or {}
	fitsinto_comparers[ka][kb] = comparer
end

local fitsinto_fail_mt = {
	__tostring = function(self)
		local message = self.message
		if type(message) == "table" then
			message = table.concat(message, "")
		end
		if self.cause then
			return message .. "." .. tostring(self.cause)
		end
		return message
	end,
}
local function fitsinto_fail(message, cause)
	if not cause and type(message) == "string" then
		if not message then
			error "missing error message for fitsinto_fail"
		end
		return message
	end
	return setmetatable({
		message = message,
		cause = cause,
	}, fitsinto_fail_mt)
end

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
local function tuple_compare(a, b)
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
			if tb.kind == "value.neutral" then
				print("value.tuple_type comparer a, b")
				print(a)
				print(b)
				p("ta, tb")
				p(ta)
				p(tb)
			end
			local ok, err = fitsinto(ta, tb)
			if not ok then
				return false, err
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
	local ok, err
	ok, err = fitsinto(a.param_type, b.param_type)
	if not ok then
		return false, fitsinto_fail("param_type", err)
	end
	local avis = a.param_info.visibility.visibility
	local bvis = b.param_info.visibility.visibility
	if avis ~= bvis and avis ~= terms.visibility.implicit then
		return false, fitsinto_fail("param_info")
	end

	local apurity = a.result_info.purity
	local bpurity = b.result_info.purity
	if apurity ~= bpurity then
		return false, fitsinto_fail("result_info")
	end

	local unique_placeholder = terms.value.neutral(terms.neutral_value.free(terms.free.unique({})))
	local a_res = apply_value(a.result_type, unique_placeholder)
	local b_res = apply_value(b.result_type, unique_placeholder)
	ok, err = fitsinto(a_res, b_res)
	if not ok then
		return false, fitsinto_fail("result_type", err)
	end
	return true
end)

for _, type_of_type in ipairs({
	value.prim_type_type,
}) do
	add_comparer(type_of_type.kind, value.star(0).kind, always_fits_comparer)
end

add_comparer(value.star(0).kind, value.star(0).kind, function(a, b)
	if a.level > b.level then
		return false, "a.level > b.level"
	end
	return true
end)

add_comparer("value.prim_boxed_type", "value.prim_boxed_type", function(a, b)
	local ok, err = fitsinto_qless(a:unwrap_prim_boxed_type(), b:unwrap_prim_boxed_type())
	return ok, err
end)

local function quantities_fitsinto(qa, qb)
	if qa == qb or qa == terms.quantity.unrestricted or qb == terms.quantity.erased then
		return true
	end
	return false, qa.kind .. " doesn't fit into " .. qb.kind
end
function fitsinto_qless(tya, tyb)
	if not fitsinto_comparers[tya.kind] then
		error("fitsinto given value a which isn't a type or NYI " .. tya.kind)
	elseif not fitsinto_comparers[tyb.kind] then
		error("fitsinto given value b which isn't a type or NYI " .. tyb.kind)
	end

	local comparer = (fitsinto_comparers[tya.kind] or {})[tyb.kind]
	if not comparer then
		return false, "no comparer for " .. tya.kind .. " with " .. tyb.kind
	end

	ok, err = comparer(tya, tyb)
	if not ok then
		return false, ".value" .. err
	end
	return true
end
function fitsinto(a, b)
	if a:is_neutral() and b:is_neutral() then
		if a == b then
			return true
		end
		return false, "both values are neutral, but they aren't equal: " .. tostring(a) .. " ~= " .. tostring(b)
	end
	if not a:is_qtype() then
		print(a)
		error("fitsinto given value a which isn't a qtype " .. a.kind)
	end
	if not b:is_qtype() then
		print(b)
		error("fitsinto given value b which isn't a qtype " .. b.kind)
	end

	local qa, tya = a:unwrap_qtype()
	local qb, tyb = b:unwrap_qtype()

	if not fitsinto_comparers[tya.kind] then
		error("fitsinto given value a which isn't a type or NYI " .. tya.kind)
	elseif not fitsinto_comparers[tyb.kind] then
		error("fitsinto given value b which isn't a type or NYI " .. tyb.kind)
	end

	local ok, err = quantities_fitsinto(qa.quantity, qb.quantity)
	if not ok then
		return false, ".quantity " .. err
	end

	local comparer = (fitsinto_comparers[tya.kind] or {})[tyb.kind]
	if not comparer then
		return false, "no comparer for " .. tya.kind .. " with " .. tyb.kind
	end

	ok, err = comparer(tya, tyb)
	if not ok then
		return false, ".value" .. err
	end
	return true
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

--[[
local function extract_value_metavariable(value) -- -> Option<metavariable>
  if value.kind == "value_neutral" and value.neutral.kind == "neutral_value_free" and value.neutral.free.kind == "free_metavariable" then
    return value.neutral.free.metavariable
  end
  return nil
end

local is_value = gen.metatable_equality(value)

local function unify(
    first_value,
    params,
    variant,
    second_value)
  -- -> unified value,
  if first_value == second_value then
    return first_value
  end

  local first_mv = extract_value_metavariable(first_value)
  local second_mv = extract_value_metavariable(second_value)

  if first_mv and second_mv then
    first_mv:bind_metavariable(second_mv)
    return first_mv:get_canonical()
  elseif first_mv then
    return first_mv:bind_value(second_value)
  elseif second_mv then
    return second_mv:bind_value(first_value)
  end

  if first_value.kind ~= second_value.kind then
    error("can't unify values of kinds " .. first_value.kind .. " and " .. second_value.kind)
  end

  local unified_args = {}
  local prefer_left = true
  local prefer_right = true
  for i, v in ipairs(params) do
    local first_arg = first_value[v]
    local second_arg = second_value[v]
    if is_value(first_arg) then
      local u = first_arg:unify(second_arg)
      unified_args[i] = u
      prefer_left = prefer_left and u == first_arg
      prefer_right = prefer_right and u == second_arg
    elseif first_arg == second_arg then
      unified_args[i] = first_arg
    else
      p("unify args", first_value, second_value)
      error("unification failure as " .. v .. " field value doesn't match")
    end
  end

  if prefer_left then
    return first_value
  elseif prefer_right then
    return second_value
  else
    -- create new value
    local first_type = getmetatable(first_value)
    local cons = first_type
    if variant then
      cons = first_type[variant]
    end
    local unified = cons(table.unpack(unified_args))
    return unified
  end
end

local unifier = {
  record = function(t, info)
    t.__index = t.__index or {}
    function t.__index:unify(second_value)
      return unify(self, info.params, nil, second_value)
    end
  end,
  enum = function(t, info)
    t.__index = t.__index or {}
    function t.__index:unify(second_value)
      local vname = string.sub(self.kind, #info.name + 2, -1)
      return unify(self, info.variants[vname].info.params, vname, second_value)
    end
  end,
}

value:derive(unifier)
result_info:derive(unifier)
]]

value:derive(derivers.eq)

---@param typechecking_context TypecheckingContext
local function check(
	checkable_term, -- constructed from checkable_term
	typechecking_context, -- todo
	target_type
) -- must be unify with target type (there is some way we can assign metavariables to make them equal)
	-- -> usage counts, a typed term
	if terms.checkable_term.value_check(checkable_term) ~= true then
		error("check, checkable_term: expected a checkable term")
	end
	if terms.typechecking_context_type.value_check(typechecking_context) ~= true then
		error("check, typechecking_context: expected a typechecking context")
	end
	if terms.value.value_check(target_type) ~= true then
		print("target_type", target_type)
		error("check, target_type: expected a target type (as an alicorn value)")
	end
	if not target_type:is_qtype() and not target_type:is_neutral() then
		print("target_type", target_type)
		error("check, target_type: expected target type to be a qtype")
	end

	if checkable_term:is_inferrable() then
		local inferrable_term = checkable_term:unwrap_inferrable()
		local inferred_type, inferred_usages, typed_term = infer(inferrable_term, typechecking_context)
		if not inferred_type:is_qtype() and not inferred_type:is_neutral() then
			print(inferrable_term)
			print(inferred_type)
			error("check: infer didn't return a qtype for " .. inferrable_term.kind)
		end
		-- TODO: unify!!!!
		if inferred_type ~= target_type then
			local ok, err
			if inferred_type:is_neutral() then
				ok, err = false, "inferred type is a neutral value"
				-- TODO: add debugging dump to typechecking context that looks for placeholders inside inferred_type
				-- then shows matching types and values in env if relevant?
			else
				ok, err = fitsinto(inferred_type, target_type)
			end
			if not ok then
				print "attempting to check if terms fit for checkable_term.inferrable"
				print("checkable_term", checkable_term)
				print("inferred_type", inferred_type)
				print("target_type", target_type)
				print("typechecking_context", typechecking_context:format_names())
				error(
					"check: mismatch in inferred and target type for "
						.. inferrable_term.kind
						.. " due to "
						.. tostring(err)
				)
			end
		end
		return inferred_usages, typed_term
	elseif checkable_term:is_tuple_cons() then
		local elements = checkable_term:unwrap_tuple_cons()

		local target_tuple_type_elements = target_type.type:unwrap_tuple_type()
		local elem_type_closures = extract_tuple_elem_type_closures(target_tuple_type_elements, value_array())
		if #elem_type_closures ~= #elements then
			print("target_type", target_type)
			print("elements", elements)
			error("check: mismatch in checkable_term.tuple_cons target type element count and elements in tuple cons")
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
		-- TODO: handle quantities
		return usages, typed_term.tuple_cons(new_elements)
	elseif checkable_term:is_prim_tuple_cons() then
		local elements = checkable_term:unwrap_prim_tuple_cons()

		local target_tuple_type_elements = target_type.type:unwrap_prim_tuple_type()
		local elem_type_closures = extract_tuple_elem_type_closures(target_tuple_type_elements, value_array())
		if #elem_type_closures ~= #elements then
			print("target_type", target_type)
			print("elements", elements)
			error(
				"check: mismatch in checkable_term.prim_tuple_cons target type element count and elements in tuple cons"
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
		-- TODO: handle quantities
		return usages, typed_term.prim_tuple_cons(new_elements)
	elseif checkable_term:is_lambda() then
		local param_name, body = checkable_term:unwrap_lambda()
		-- assert that target_type is a pi type
		-- TODO open says work on other things first they will be easier
		error("nyi")
	else
		error("check: unknown kind: " .. checkable_term.kind)
	end

	error("unreachable!?")
end

function apply_value(f, arg)
	if terms.value.value_check(f) ~= true then
		error("apply_value, f: expected an alicorn value")
	end
	if terms.value.value_check(arg) ~= true then
		error("apply_value, arg: expected an alicorn value")
	end

	if f:is_closure() then
		local code, capture = f:unwrap_closure()
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
	if not subject_type:is_qtype() then
		print("missing qtype wrapping tuple type")
		print(subject_type:pretty_print())
	end
	-- define how the type of each tuple element should be evaluated
	local qty, base = subject_type:unwrap_qtype()
	return infer_tuple_type_unwrapped(base, subject_value)
end

local function nearest_star_level(typ)
	if typ:is_prim_type_type() then
		return 0
	elseif typ:is_star() then
		return typ:unwrap_star()
	else
		error "unknown sort in nearest_star, please expand or build a proper least upper bound"
	end
end

---@param inferrable_term unknown
---@param typechecking_context TypecheckingContext
---@return unknown, unknown, unknown
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
		local checkable_term, inferrable_target_type = inferrable_term:unwrap_annotated()
		local type_of_type, usages, target_typed_term = infer(inferrable_target_type, typechecking_context)
		local target_type = evaluate(target_typed_term, typechecking_context.runtime_context)
		return target_type, check(checkable_term, typechecking_context, target_type)
	elseif inferrable_term:is_typed() then
		return inferrable_term:unwrap_typed()
	elseif inferrable_term:is_annotated_lambda() then
		local param_name, param_annotation, body, anchor = inferrable_term:unwrap_annotated_lambda()
		local _, _, param_term = infer(param_annotation, typechecking_context)
		local param_qtype = evaluate(param_term, typechecking_context:get_runtime_context())
		-- TODO: also handle neutral values, for inference of qtype
		local param_quantity, param_type = param_qtype:unwrap_qtype()
		local param_quantity = param_quantity:unwrap_quantity()
		local inner_context = typechecking_context:append(param_name, param_qtype, nil, anchor)
		local body_type, body_usages, body_term = infer(body, inner_context)
		local result_type = substitute_type_variables(body_type, #inner_context)
		local body_usages_param = body_usages[#body_usages]
		local lambda_usages = body_usages:copy(1, #body_usages - 1)
		if param_quantity:is_erased() then
			if body_usages_param > 0 then
				error("infer: trying to use an erased parameter")
			end
		elseif param_quantity:is_linear() then
			if body_usages_param > 1 then
				error("infer: trying to use a linear parameter multiple times")
			end
		elseif param_quantity:is_unrestricted() then
		-- nwn
		else
			error("infer: unknown quantity")
		end
		local lambda_type = value.pi(param_qtype, param_info_explicit, result_type, result_info_pure)
		local lambda_term = typed_term.lambda(body_term)
		-- TODO: handle quantities
		return unrestricted(lambda_type), lambda_usages, lambda_term
	elseif inferrable_term:is_qtype() then
		local quantity, t = inferrable_term:unwrap_qtype()
		local quantity_type, quantity_usages, quantity_term = infer(quantity, typechecking_context)
		local type_type, type_usages, type_term = infer(t, typechecking_context)
		if type_type:is_qtype_type() then
			error("inferrable_term.qtype wrapping another qtype")
		end
		local qtype_usages = usage_array()
		add_arrays(qtype_usages, quantity_usages)
		add_arrays(qtype_usages, type_usages)
		local qtype = typed_term.qtype(quantity_term, type_term)
		local qtype_type = value.qtype_type(get_level(type_type))
		-- print("inferring a qtype")
		-- print(inferrable_term:pretty_print())
		-- print(qtype:pretty_print())
		return qtype_type, qtype_usages, qtype
	elseif inferrable_term:is_pi() then
		error("infer: nyi")
		local param_type, param_info, result_type, result_info = inferrable_term:unwrap_pi()
		local param_type_type, param_type_usages, param_type_term = infer(param_type, typechecking_context)
		local param_info_usages, param_info_term = check(param_info, typechecking_context, value.param_info_type)
		local result_type_type, result_type_usages, result_type_term = infer(result_type, typechecking_context)
		local result_info_usages, result_info_term = check(result_info, typechecking_context, value.result_info_type)
		local result_type_type_quantity, result_type_type_base = result_type_type:unwrap_qtype()
		if not result_type_type_base:is_pi() then
			error "result type of a pi term must infer to a pi because it must be callable"
			-- TODO: switch to using a mechanism term system
		end
		local result_type_param_type, result_type_param_info, result_type_result_type, result_type_result_info =
			result_type_type_base:unwrap_pi()

		if not result_type_result_info:unwrap_result_info():is_pure() then
			error "result type computation must be pure for now"
		end

		local ok, err =
			fitsinto(evaluate(param_type_term, typechecking_context.runtime_context), result_type_param_type)
		if not ok then
			error(
				"inferrable pi type's param type doesn't fit into the result type function's parameters because " .. err
			)
		end
		local sort =
			value.star(math.max(nearest_star_level(param_type_type), nearest_star_level(result_type_result_type), 0))

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
		--FIXME: f_quantity is unused
		local f_quantity, f_type = f_type:unwrap_qtype()

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

			-- check already checked for us so no fitsinto
			local arg_value = evaluate(arg_term, typechecking_context:get_runtime_context())
			local application_result_type = apply_value(f_result_type, arg_value)

			print("arg_value", arg_value)
			print("f_result_type", f_result_type)
			print("application_result_type", application_result_type)
			if value.value_check(application_result_type) ~= true then
				local bindings = typechecking_context:get_runtime_context().bindings
				-- for i = 1, bindings:len() do
				-- 	print("runtime_context.bindings." .. tostring(i), bindings:get(i))
				-- end
				error("application_result_type isn't a value inferring application of pi type")
			end
			return application_result_type, application_usages, application
		elseif f_type:is_prim_function_type() then
			print "inferring application of primitive function"
			print("typechecking_context")
			typechecking_context:dump_names()
			print(f_type:pretty_print())
			print(arg:pretty_print())
			local f_param_type, f_result_type_closure = f_type:unwrap_prim_function_type()

			local arg_usages, arg_term = check(arg, typechecking_context, f_param_type)

			local application_usages = usage_array()
			add_arrays(application_usages, f_usages)
			add_arrays(application_usages, arg_usages)
			local application = typed_term.application(f_term, arg_term)

			-- check already checked for us so no fitsinto
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
				tup_val(type_data, substitute_type_variables(el_type, #typechecking_context + 1))
			)
			add_arrays(usages, el_usages)
			new_elements:append(el_term)
		end
		-- TODO: handle quantities
		return unrestricted(value.tuple_type(type_data)), usages, typed_term.tuple_cons(new_elements)
	elseif inferrable_term:is_prim_tuple_cons() then
		print "inferring tuple construction"
		print(inferrable_term:pretty_print())
		print "environment_names"
		for i = 1, #typechecking_context do
			print(i, typechecking_context:get_name(i))
		end
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
			print "inferring element of tuple construction"
			print(el_type:pretty_print())
			type_data = value.enum_value(
				"cons",
				tup_val(type_data, substitute_type_variables(el_type, #typechecking_context + 1))
			)
			add_arrays(usages, el_usages)
			new_elements:append(el_term)
		end
		-- TODO: handle quantities
		return unrestricted(value.prim_tuple_type(type_data)), usages, typed_term.prim_tuple_cons(new_elements)
	elseif inferrable_term:is_tuple_elim() then
		local subject, body = inferrable_term:unwrap_tuple_elim()
		local subject_type, subject_usages, subject_term = infer(subject, typechecking_context)
		--local subject_quantity, subject_type = subject_type:unwrap_qtype()

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
		return body_type, result_usages, typed_term.tuple_elim(subject_term, n_elements, body_term)
	elseif inferrable_term:is_tuple_type() then
		local definition = inferrable_term:unwrap_tuple_type()
		local definition_type, definition_usages, definition_term = infer(definition, typechecking_context)
		--local def_qty, def_base = definition_type:unwrap_qtype()
		if definition_type ~= terms.value.tuple_defn_type then
			error "argument to tuple_type is not a tuple_defn"
		end
		return unrestricted(terms.value.star(0)), definition_usages, terms.typed_term.tuple_type(definition_term)
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
				tup_val(type_data, value.name(k), substitute_type_variables(field_type, #typechecking_context + 1))
			)
			add_arrays(usages, field_usages)
			new_fields[k] = field_term
		end
		-- TODO: handle quantities
		return unrestricted(value.record_type(type_data)), usages, typed_term.record_cons(new_fields)
	elseif inferrable_term:is_record_elim() then
		local subject, field_names, body = inferrable_term:unwrap_record_elim()
		local subject_type, subject_usages, subject_term = infer(subject, typechecking_context)
		local subject_quantity, subject_type = subject_type:unwrap_qtype()
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
		-- local subject_quantity, subject_type = subject_type:unwrap_qtype()
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
		return unrestricted(value.object_type(type_data)), usages_array(), typed_term.object_cons(new_methods)
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
		if userdata_type ~= op_userdata_type and not fitsinto(userdata_type, op_userdata_type) then
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
		local goal_type = unrestricted(value.pi(
			unrestricted(
				value.tuple_type(
					cons(
						cons(empty, const_combinator(unrestricted(prim_syntax_type))),
						const_combinator(unrestricted(prim_environment_type))
					)
				)
			),
			--unrestricted(tup_val(unrestricted(prim_syntax_type), unrestricted(prim_environment_type))),
			param_info_explicit,
			const_combinator(
				unrestricted(
					value.tuple_type(
						cons(
							cons(empty, const_combinator(unrestricted(prim_inferrable_term_type))),
							const_combinator(unrestricted(prim_environment_type))
						)
					)
				)
			),
			--unrestricted(tup_val(unrestricted(prim_inferrable_term_type), unrestricted(prim_environment_type))),
			result_info_pure
		))
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
	elseif inferrable_term:is_prim_boxed_type() then
		local type_inf = inferrable_term:unwrap_prim_boxed_type()
		local content_type_type, content_type_usages, content_type_term = infer(type_inf, typechecking_context)
		if not is_type_of_types(content_type_type) then
			error "infer: type being boxed must be a type"
		end
		local quantity, backing_type = content_type_type:unwrap_qtype()
		return value.qtype(quantity, value.prim_type_type),
			content_type_usages,
			typed_term.prim_boxed_type(content_type_term)
	elseif inferrable_term:is_prim_box() then
		local content = inferrable_term:unwrap_prim_box()
		local content_type, content_usages, content_term = infer(content, typechecking_context)
		local quantity, backing_type = content_type:unwrap_qtype()
		return value.qtype(quantity, value.prim_boxed_type(backing_type)),
			content_usages,
			typed_term.prim_box(content_term)
	elseif inferrable_term:is_prim_unbox() then
		local container = inferrable_term:unwrap_prim_unbox()
		local container_type, container_usages, container_term = infer(container, typechecking_context)
		local quantity, backing_type = container_type:unwrap_qtype()
		local content_type = backing_type:unwrap_prim_boxed_type()
		return value.qtype(quantity, content_type), container_usages, typed_term.prim_unbox(container_term)
	elseif inferrable_term:is_prim_if() then
		local subject, consequent, alternate = inferrable_term:unwrap_prim_if()
		-- for each thing in typechecking context check if it == the subject, replace with literal true
		-- same for alternate but literal false

		local stype, susages, sterm = check(terms.value.prim_bool_type, subject, typechecking_context)
		local ctype, cusages, cterm = infer(consequent, typechecking_context)
		local atype, ausages, aterm = infer(alternate, typechecking_context)
		local resulting_type
		if ctype == atype or (fitsinto(ctype, atype) and fitsinto(atype, ctype)) then
			resulting_type = ctype
		else
			p(ctype, atype)
			error("types of sides of prim_if aren't castable")
		end
		local result_usages = usage_array()
		add_arrays(result_usages, susages)
		-- FIXME: max of cusages and ausages rather than adding?
		add_arrays(result_usages, cusages)
		add_arrays(result_usages, ausages)
		return resulting_type, result_usages, typed_term.prim_if(sterm, cterm, aterm)
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
		return bodytype, result_usages, terms.typed_term.let(exprterm, bodyterm)
	elseif inferrable_term:is_prim_intrinsic() then
		local source, type = inferrable_term:unwrap_prim_intrinsic()
		local source_usages, source_term = check(source, typechecking_context, unrestricted(value.prim_string_type))
		local type_type, type_usages, type_term = infer(type, typechecking_context) --check(type, typechecking_context, value.qtype_type(0))

		print "prim intrinsic is inferring"
		print(type:pretty_print())
		print("lowers to")
		print(type_term:pretty_print())
		--error "weird type"
		-- FIXME: type_type, source_type are ignored, need checked?
		local type_val = evaluate(type_term, typechecking_context.runtime_context)
		return type_val, source_usages, typed_term.prim_intrinsic(source_term)
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
---@param base Value
---@param original Value
---@param replacement Value
local function substitute_value(base, original, replacement)
	if base == original then
		return replacement
	end
	if base:is_pi() then
		local param_type, param_info, result_type, result_info = base:unwrap_pi()
	end
end

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
		return value.closure(typed_term:unwrap_lambda(), runtime_context)
	elseif typed_term:is_qtype() then
		local quantity, type_term = typed_term:unwrap_qtype()
		local quantity_value = evaluate(quantity, runtime_context)
		local type_value = evaluate(type_term, runtime_context)
		if type_value:is_qtype() then
			print("type_term", type_term)
			print("type_value (evaluate(type_term))", type_value)
			error "typed_term.qtype wrapping another qtype"
		end
		return value.qtype(quantity_value, type_value)
	elseif typed_term:is_pi() then
		local param_type, param_info, result_type, result_info = typed_term:unwrap_pi()
		local param_type_value = evaluate(param_type, runtime_context)
		local param_info_value = evaluate(param_info, runtime_context)
		local result_type_value = evaluate(result_type, runtime_context)
		local result_info_value = evaluate(result_info, runtime_context)
		return value.pi(param_type_value, param_info_value, result_type_value, result_info_value)
	elseif typed_term:is_application() then
		local f, arg = typed_term:unwrap_application()
		local f_value = evaluate(f, runtime_context)
		local arg_value = evaluate(arg, runtime_context)
		return apply_value(f_value, arg_value)
	elseif typed_term:is_tuple_cons() then
		local elements = typed_term:unwrap_tuple_cons()
		local new_elements = value_array()
		for _, v in ipairs(elements) do
			new_elements:append(evaluate(v, runtime_context))
		end
		return value.tuple_value(new_elements)
	elseif typed_term:is_prim_tuple_cons() then
		local elements = typed_term:unwrap_prim_tuple_cons()
		local new_elements = primitive_array()
		local stuck = false
		local stuck_element
		local trailing_values
		for _, v in ipairs(elements) do
			local element_value = evaluate(v, runtime_context)
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
		local subject, length, body = typed_term:unwrap_tuple_elim()
		local subject_value = evaluate(subject, runtime_context)
		local inner_context = runtime_context
		if subject_value:is_tuple_value() then
			local subject_elements = subject_value:unwrap_tuple_value()
			if #subject_elements ~= length then
				error("evaluate: mismatch in tuple length from typechecking and evaluation")
			end
			for i = 1, length do
				inner_context = inner_context:append(subject_elements[i])
			end
		elseif subject_value:is_prim_tuple_value() then
			local subject_elements = subject_value:unwrap_prim_tuple_value()
			if #subject_elements ~= length then
				p(#subject_elements, length)
				error("evaluate: mismatch in tuple length from typechecking and evaluation")
			end
			for i = 1, length do
				inner_context = inner_context:append(value.prim(subject_elements[i]))
			end
		elseif subject_value:is_neutral() then
			local subject_neutral = subject_value:unwrap_neutral()
			for i = 1, length do
				inner_context =
					inner_context:append(value.neutral(neutral_value.tuple_element_access_stuck(subject_neutral, i)))
			end
		else
			p(subject_value)
			error("evaluate, is_tuple_elim, subject_value: expected a tuple")
		end
		return evaluate(body, inner_context)
	elseif typed_term:is_tuple_element_access() then
		local tuple_term, index = typed_term:unwrap_tuple_element_access()
		print("tuple_element_access tuple_term", tuple_term)
		local tuple = evaluate(tuple_term, runtime_context)
		print("tuple_element_access tuple_term", tuple)
		return index_tuple_value(tuple, index)
	elseif typed_term:is_tuple_type() then
		local definition_term = typed_term:unwrap_tuple_type()
		local definition = evaluate(definition_term, runtime_context)
		return terms.value.tuple_type(definition)
	elseif typed_term:is_record_cons() then
		local fields = typed_term:unwrap_record_cons()
		local new_fields = string_value_map()
		for k, v in pairs(fields) do
			new_fields[k] = evaluate(v, runtime_context)
		end
		return value.record_value(new_fields)
	elseif typed_term:is_record_elim() then
		local subject, field_names, body = typed_term:unwrap_record_elim()
		local subject_value = evaluate(subject, runtime_context)
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
		return evaluate(body, inner_context)
	elseif typed_term:is_enum_cons() then
		local constructor, arg = typed_term:unwrap_enum_cons()
		local arg_value = evaluate(arg, runtime_context)
		return value.enum_value(constructor, arg_value)
	elseif typed_term:is_enum_elim() then
		local subject, mechanism = typed_term:unwrap_enum_elim()
		local subject_value = evaluate(subject, runtime_context)
		local mechanism_value = evaluate(mechanism, runtime_context)
		if subject_value:is_enum_value() then
			if mechanism_value:is_object_value() then
				local constructor, arg = subject_value:unwrap_enum_value()
				local methods, capture = mechanism_value:unwrap_object_value()
				local this_method = value.closure(methods[constructor], capture)
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
				local this_method = value.closure(methods[constructor], capture)
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
	elseif typed_term:is_prim_boxed_type() then
		local type_term = typed_term:unwrap_prim_boxed_type()
		local type_value = evaluate(type_term, runtime_context)
		local quantity, backing_type = type_value:unwrap_qtype()
		return value.prim_boxed_type(backing_type)
	elseif typed_term:is_prim_box() then
		local content = typed_term:unwrap_prim_box()
		return value.prim(evaluate(content, runtime_context))
	elseif typed_term:is_prim_unbox() then
		local unwrapped = typed_term:unwrap_prim_unbox()
		local unwrap_val = evaluate(unwrapped, runtime_context)
		if not unwrap_val.as_prim then
			print("unwrapped", unwrapped, unwrap_val)
			error "evaluate, is_prim_unbox: missing as_prim on unwrapped prim_unbox"
		end
		if unwrap_val:is_prim() then
			return unwrap_val:unwrap_prim()
		elseif unwrap_val:is_neutral() then
			local nval = unwrap_val:unwrap_neutral()
			return value.neutral(neutral_value.prim_unbox_stuck(nval))
		else
			print("unrecognized value in unbox", unwrap_val)
			error "invalid value in unbox, must be prim or neutral"
		end
	elseif typed_term:is_let() then
		local expr, body = typed_term:unwrap_let()
		local expr_value = evaluate(expr, runtime_context)
		return evaluate(body, runtime_context:append(expr_value))
	elseif typed_term:is_prim_intrinsic() then
		local source = typed_term:unwrap_prim_intrinsic()
		local source_val = evaluate(source, runtime_context)
		if source_val:is_prim() then
			local source_str = source_val:unwrap_prim()
			return value.prim(assert(load(source_str, "prim_intrinsic", "t", {
				assert = assert,
				p = p,
				print = print,
				terms = terms,
				terms_gen = gen,
			}))())
		elseif source_val:is_neutral() then
			local source_neutral = source_val:unwrap_neutral()
			return value.neutral(neutral_value.prim_intrinsic_stuck(source_neutral))
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
		if previous_level.level > 10 then
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
    if previous_level.level > 10 then
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

return {
	fitsinto = fitsinto,
	extract_tuple_elem_type_closures = extract_tuple_elem_type_closures,
	const_combinator = const_combinator,
	check = check,
	infer = infer,
	infer_tuple_type = infer_tuple_type,
	evaluate = evaluate,
	apply_value = apply_value,
	index_tuple_value = index_tuple_value,
}
