-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

local terms = require "terms"
local metalanguage = require "metalanguage"
local U = require "alicorn-utils"
local flex_runtime_context = terms.flex_runtime_context
local pretty_printer = require "pretty-printer"
local s = pretty_printer.s
--local new_typechecking_context = terms.typechecking_context
--local checkable_term = terms.checkable_term
--local inferrable_term = terms.inferrable_term
local typed_term = terms.typed_term
local free = terms.free
local visibility = terms.visibility
local purity = terms.purity
local result_info = terms.result_info
local flex_value = terms.flex_value
local strict_value = terms.strict_value
local stuck_value = terms.stuck_value
local host_syntax_type = terms.host_syntax_type
local host_environment_type = terms.host_environment_type
local host_typed_term_type = terms.host_typed_term_type
local host_goal_type = terms.host_goal_type
local host_inferrable_term_type = terms.host_inferrable_term_type

local diff = require "traits".diff

local gen = require "terms-generators"
local map = gen.declare_map
local string_typed_map = map(gen.builtin_string, typed_term)
local string_value_map = map(gen.builtin_string, flex_value)
local array = gen.declare_array
local typed_array = array(typed_term)
local flex_value_array = array(flex_value)
local host_array = array(gen.any_lua_type)
local usage_array = array(gen.builtin_number)
local string_array = array(gen.builtin_string)
local debug_array = array(terms.var_debug)

local internals_interface = require "internals-interface"

local eval_types = require "evaluator-types"
local subtype_relation_mt, SubtypeRelation, EdgeNotif =
	eval_types.subtype_relation_mt, eval_types.SubtypeRelation, eval_types.EdgeNotif

local param_info_explicit = flex_value.param_info(flex_value.visibility(visibility.explicit))
local result_info_pure = flex_value.result_info(result_info(purity.pure))

local OMEGA = 9
local typechecker_state
local name_array = string_array
local typed = terms.typed_term

---@source evaluator.lua
local apply_value

---@source evaluator.lua
local evaluate

---@source evaluator.lua
local infer

---@class ConstraintError
---@field desc string
---@field left flex_value
---@field l_ctx any
---@field op string
---@field right flex_value
---@field r_ctx any
---@field cause any
local ConstraintError = {}

local constraint_error_mt = {
	__tostring = function(self)
		local s = self.desc .. " " .. self.left:pretty_print(self.l_ctx) .. " "
		if self.right then
			s = s .. self.op .. " " .. self.right:pretty_print(self.r_ctx)
		end
		if self.cause then
			s = s .. " caused by " .. tostring(self.cause)
		end
		return s
	end,
	__index = ConstraintError,
}

---@param desc string
---@param left flex_value
---@param l_ctx any
---@param op string?
---@param right flex_value?
---@param r_ctx any?
---@param cause any?
---@return ConstraintError
function ConstraintError.new(desc, left, l_ctx, op, right, r_ctx, cause)
	return setmetatable({
		desc = desc,
		left = left,
		l_ctx = l_ctx,
		op = op,
		right = right,
		r_ctx = r_ctx,
		cause = cause,
	}, constraint_error_mt)
end

---@param luafunc function
---@return strict_value
local function luatovalue(luafunc)
	local luafunc_debug = debug.getinfo(luafunc, "u")
	local parameters = name_array()
	local params_dbg = debug_array()
	local len = luafunc_debug.nparams
	local new_body = typed_array()

	local arg_dbg = terms.var_debug("#host-arg", U.anchor_here())
	for i = 1, len do
		local param_name = debug.getlocal(luafunc, i)
		local param_dbg = terms.var_debug(param_name, U.anchor_here())
		parameters:append(param_name)
		params_dbg:append(param_dbg)
		new_body:append(typed.bound_variable(i + 1, param_dbg))
	end

	return strict_value.closure(
		"#luatovalue-args",
		typed.application(
			typed.literal(strict_value.host_value(luafunc)),
			typed.tuple_elim(
				parameters,
				params_dbg,
				typed.bound_variable(1, arg_dbg),
				len,
				typed.host_tuple_cons(new_body)
			)
		),
		terms.strict_runtime_context(),
		arg_dbg
	)
end

---builds a nested cause and propagates track
---@param desc string
---@param cause constraintcause
---@param val flex_value
---@param use flex_value
---@return constraintcause
local function nestcause(desc, cause, val, use, val_ctx, use_ctx)
	local r = terms.constraintcause.nested(desc, cause)
	r.track = cause.track
	--if r.track then
	r.val = val
	r.val_ctx = val_ctx
	r.use = use
	r.use_ctx = use_ctx
	--end
	return r
end

---builds a composite cause and propagates track
---@param kind string
---@param l_index number
---@param l ConstrainEdge
---@param r_index number
---@param r ConstrainEdge
---@param anchor Anchor
---@return constraintcause
local function compositecause(kind, l_index, l, r_index, r, anchor)
	local cause = terms.constraintcause[kind](l_index, r_index, anchor)
	if l.track or r.track then
		cause.track = true
	end
	return cause
end

--- lifts a subtyping relation (λ(a, b). Rel(a, b)) to (λ(f, g). ∀x. Rel(f(x), g(x))).
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
		constrain = luatovalue(function(l_ctx, val, r_ctx, use, cause)
			local inner_info = {
				debug = "FunctionRelation(" .. srel.debug_name .. ").constrain " .. U.here(),
				--.. " caused by: "
				--.. U.strip_ansi(tostring(cause)),
			}
			local u = flex_value.stuck(stuck_value.free(free.unique(inner_info)))

			local applied_val = apply_value(val, u, l_ctx)
			local applied_use = apply_value(use, u, r_ctx)

			--[[local applied_val = U.tag(
				"apply_value",
				{ val = val:pretty_preprint(l_ctx), use = use:pretty_preprint(r_ctx) },
				apply_value,
				val,
				u
			)
			local applied_use = U.tag(
				"apply_value",
				{ val = val:pretty_preprint(l_ctx), use = use:pretty_preprint(r_ctx) },
				apply_value,
				use,
				u
			)]]

			typechecker_state:queue_constrain(
				l_ctx,
				applied_val,
				srel,
				r_ctx,
				applied_use,
				nestcause("FunctionRelation inner", cause, applied_val, applied_use, l_ctx, r_ctx)
			)

			return true
		end),
	}, subtype_relation_mt)
end
FunctionRelation = U.memoize(FunctionRelation)

---independent tuple relation.
---takes variances from a tuple of arguments to a type family.
---propagates agreement between those variances to the tuple of arguments as a whole.
---
---(in lieu of future `TupleRelation` that will be capable of handling dependent tuples.)
---@param ... Variance
---@return SubtypeRelation
local function IndepTupleRelation(...)
	local args = { ... }
	---@type string[]
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
			---@param l_ctx TypecheckingContext
			---@param val flex_value
			---@param r_ctx TypecheckingContext
			---@param use flex_value
			---@param cause constraintcause
			---@return boolean
			function(l_ctx, val, r_ctx, use, cause)
				local val_elems = val:unwrap_tuple_value()
				local use_elems = use:unwrap_tuple_value()
				for i = 1, val_elems:len() do
					if args[i].positive then
						typechecker_state:queue_constrain(
							l_ctx,
							val_elems[i],
							args[i].srel,
							r_ctx,
							use_elems[i],
							nestcause(
								"positive tuple element constraint",
								cause,
								val_elems[i],
								use_elems[i],
								l_ctx,
								r_ctx
							)
						)
					else
						typechecker_state:queue_constrain(
							r_ctx,
							use_elems[i],
							args[i].srel,
							l_ctx,
							val_elems[i],
							nestcause(
								"negative tuple element constraint",
								cause,
								use_elems[i],
								val_elems[i],
								l_ctx,
								r_ctx
							)
						)
					end
				end

				return true
			end
		),
	}, subtype_relation_mt)
end
IndepTupleRelation = U.memoize(IndepTupleRelation)

---@type SubtypeRelation
local EffectRowRelation = setmetatable({
	debug_name = "EffectRowRelation",
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
		---@param l_ctx TypecheckingContext
		---@param val flex_value
		---@param r_ctx TypecheckingContext
		---@param use flex_value
		---@param cause constraintcause
		---@return boolean, string?
		function(l_ctx, val, r_ctx, use, cause)
			if val:is_effect_empty() then
				return true
			end
			if val:is_effect_row_extend() then
				local val_components, val_rest = val:unwrap_effect_row_extend()
				if use:is_effect_empty() then
					return false, "production has effect requirements that the consumption doesn't fulfill"
				end
				if not use:is_effect_row_extend() then
					return false, "consumption of effect row constraint isn't an effect row?"
				end
				local use_components, use_rest = use:unwrap_effect_row_extend()
				if not use_components:superset(val_components) then
					return false, "consumption of effect row doesn't satisfy all components of production"
				end
				--TODO allow polymorphism
				if val_rest:is_effect_empty() and use_rest:is_effect_empty() then
					return true
				end
				error "NYI effect polymorphism"
			end

			return true
		end
	),
}, subtype_relation_mt)

---@source evaluator.lua
local UniverseOmegaRelation

---@type SubtypeRelation
local EnumDescRelation = setmetatable({
	debug_name = "EnumDescRelation",
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
		---@param l_ctx TypecheckingContext
		---@param val flex_value
		---@param r_ctx TypecheckingContext
		---@param use flex_value
		---@param cause constraintcause
		---@return boolean, string?
		function(l_ctx, val, r_ctx, use, cause)
			if not val:is_enum_desc_value() then
				error "production is not an enum description"
			end
			local val_variants = val:unwrap_enum_desc_value()
			if not use:is_enum_desc_value() then
				error "consumption is not an enum description"
			end
			local use_variants = use:unwrap_enum_desc_value()
			for name, val_type in val_variants:pairs() do
				local use_variant = use_variants:get(name)
				if use_variant == nil then
					local smallest = 99999999999
					local suggest = "[enum has no variants!]"
					for n, _ in use_variants:pairs() do
						local d = U.levenshtein(name, n)
						if d < smallest then
							smallest, suggest = d, n
						end
					end
					error(name .. " is not a valid enum variant! Did you mean " .. suggest .. "?")
				end
				typechecker_state:queue_subtype(
					l_ctx,
					val_type,
					r_ctx,
					use_variant --[[@as flex_value -- please find a better approach]],
					nestcause("enum variant", cause, val_type, use_variant, l_ctx, r_ctx)
				)
			end
			return true
		end
	),
}, subtype_relation_mt)

---@source evaluator.lua
local infer_tuple_type_unwrapped2

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
		---@param l_ctx TypecheckingContext
		---@param val flex_value
		---@param r_ctx TypecheckingContext
		---@param use flex_value
		---@param cause constraintcause
		---@return boolean
		function(l_ctx, val, r_ctx, use, cause)
			-- FIXME: this should probably be handled elsewhere
			if val:is_stuck() and val == use then
				return true
			end
			-- FIXME: this is quick'n'dirty copypaste, slightly edited to jankily call existing code
			-- this HAPPENS to work
			-- this WILL need to be refactored
			-- i have considered exploiting the linked-list structure of tuple desc for recursive
			-- checking, but doing it naively won't work because the unique (representing the tuple
			-- value) should be the same across the whole desc
			local unique = { debug = "TupleDescRelation.constrain" .. U.here() .. " value_placeholder" }
			local value_placeholder = flex_value.stuck(stuck_value.free(free.unique(unique)))
			local ok, tuple_types_val, tuple_types_use, tuple_vals, n = infer_tuple_type_unwrapped2(
				flex_value.tuple_type(val),
				l_ctx,
				flex_value.tuple_type(use),
				r_ctx,
				value_placeholder
			)

			if not ok then
				if tuple_types_val == "length-mismatch" then
					error(
						ConstraintError.new(
							"Tuple lengths do not match: ",
							flex_value.tuple_type(val),
							l_ctx,
							"!=",
							flex_value.tuple_type(use),
							r_ctx
						)
					)
				else
					error(tuple_types_val)
				end
			end

			for i = 1, n do
				typechecker_state:queue_subtype(
					l_ctx,
					tuple_types_val[i],
					l_ctx,
					tuple_types_use[i],
					nestcause(
						"TupleDescRelation.constrain " .. tostring(i),
						cause,
						tuple_types_val[i],
						tuple_types_use[i],
						l_ctx,
						r_ctx
					)
				)
			end

			return true
		end
	),
}, subtype_relation_mt)

---@param onto ArrayValue
---@param with ArrayValue
local function add_arrays(onto, with)
	local o_len = onto:len()
	for i, n in with:ipairs() do
		local x
		if i > o_len then
			x = 0
		else
			x = onto[i]
		end
		onto[i] = x + n
	end
end

---make an alicorn function that returns the specified values
---@param v strict_value
---@return strict_value
local function const_combinator(v)
	local d_info = terms.var_debug("#CONST_PARAM", U.anchor_here())
	return U.notail(
		strict_value.closure(
			d_info.name,
			typed_term.bound_variable(1, d_info),
			terms.strict_runtime_context():append(v, d_info.name, d_info),
			d_info
		)
	)
end

---@param t flex_value
---@return integer
local function get_level(t)
	-- TODO: this
	-- TODO: typecheck
	return 0
end

---@param v table
---@param ctx TypecheckingContext
---@return boolean
local function verify_placeholder_lite(v, ctx, nested)
	-- If it's not a table we don't care
	if type(v) ~= "table" then
		return true
	end

	-- Special handling for arrays
	if getmetatable(v) and getmetatable(getmetatable(v)) == gen.array_type_mt then
		for k, val in ipairs(v) do
			local ok, i, info, info_mismatch = verify_placeholder_lite(val, ctx, true)
			if not ok then
				if not nested then
					print(v)
					if info_mismatch ~= nil then
						print("EXPECTED INFO: " .. info_mismatch)
					end
					error("AAAAAAAAAAAAAA found " .. tostring(i))
				end
				return false, i, info
			end
		end
		return true
	end
	if not v.kind then
		return true
	end

	if v.kind == "free.placeholder" then
		local i, info = v:unwrap_placeholder()
		if i > ctx:len() or i > ctx.runtime_context.bindings:len() then
			--os.exit(-1, true)
			--error("AAAAAAAAAAAAAA found " .. tostring(i) .. " " .. tostring(info))
			return false, i, info
		end
		local info_target = ctx.runtime_context.bindings:get(i).debuginfo
		if info ~= info_target then
			return false, i, info, info_target
		end
	end

	for k, val in pairs(v) do
		if k ~= "cause" and k ~= "bindings" and k ~= "provenance" then
			local ok, i, info, info_mismatch = verify_placeholder_lite(val, ctx, true)
			if not ok then
				if not nested then
					print(v)
					if info_mismatch ~= nil then
						print("EXPECTED INFO: " .. info_mismatch)
					end
					error("AAAAAAAAAAAAAA found " .. tostring(i) .. " " .. tostring(info))
				end
				return false, i, info
			end
		end
	end

	return true
end

local orig_literal_constructor = typed_term.literal
local function literal_constructor_check(val)
	-- FIXME: make sure no placeholders in val
	verify_placeholder_lite(val, terms.typechecking_context())
	return orig_literal_constructor(val)
end
typed_term.literal = literal_constructor_check

---@param v table
---@param ctx FlexRuntimeContext
---@return boolean
local function verify_closure(v, ctx, nested)
	-- If it's not a table we don't care
	if type(v) ~= "table" then
		return true
	end

	-- Special handling for arrays
	if getmetatable(v) and getmetatable(getmetatable(v)) == gen.array_type_mt then
		for k, val in ipairs(v) do
			local ok, i, info = verify_closure(val, ctx, true)
			if not ok then
				if not nested then
					error("Invalid bound variable with index " .. tostring(i) .. ": " .. tostring(info))
				end
				return false, i, info
			end
		end
		return true
	end
	if not v.kind then
		return true
	end

	if v.kind == "typed.let" then
		return true -- we can't check these right now
	end

	if v.kind == "stuck_value.closure" then
		-- If the closure contains another closure we need to switch contexts
		local param_name, code, capture, debug = v:unwrap_closure()
		return verify_closure(code, capture, true)
	end

	if v.kind == "strict_value.closure" then
		-- If the closure contains another closure we need to switch contexts
		local param_name, code, capture, debug = v:unwrap_closure()
		return verify_closure(code, capture:as_flex(), true)
	end

	if v.kind == "typed.bound_variable" then
		local idx, b_dbg = v:unwrap_bound_variable()
		local rc_val, c_dbg = ctx:get(idx)
		if rc_val == nil then
			return true -- TODO: Can we actually validate this?
			--return false, idx, "runtime_context:get() for bound_variable returned nil"
		end
		if b_dbg ~= c_dbg then
			local info = "Debug information doesn't match! Contexts are mismatched! Variable #"
				.. tostring(v["{ID}"])
				.. " thinks it is getting "
				.. tostring(b_dbg)
				.. " but context thinks it has "
				.. tostring(c_dbg)
				.. " at index "
				.. tostring(idx)

			return false, idx, info
		end
	end

	for k, val in pairs(v) do
		if k ~= "cause" and k ~= "bindings" and k ~= "provenance" then
			local ok, i, info = verify_closure(val, ctx, true)
			if not ok then
				if not nested then
					error("Invalid bound variable with index " .. tostring(i) .. ": " .. tostring(info))
				end
				return false, i, info
			end
		end
	end

	return true
end

local orig_strict_closure_constructor = strict_value.closure
local function strict_closure_constructor_check(param_name, code, capture, debug)
	verify_closure(code, capture:as_flex())
	return U.notail(orig_strict_closure_constructor(param_name, code, capture, debug))
end
strict_value.closure = strict_closure_constructor_check

local orig_stuck_closure_constructor = stuck_value.closure
local function stuck_closure_constructor_check(param_name, code, capture, debug)
	verify_closure(code, capture)
	return U.notail(orig_stuck_closure_constructor(param_name, code, capture, debug))
end
stuck_value.closure = stuck_closure_constructor_check

---@source evaluator.lua
local substitute_inner

---@param val flex_value an alicorn value
---@param mappings {[integer|flex_value]: typed} the placeholder we are trying to get rid of by substituting
---@param context_len integer number of bindings in the runtime context already used - needed for closures
---@param ambient_typechecking_context TypecheckingContext
---@return typed a typed term
local function substitute_inner_impl(val, mappings, context_len, ambient_typechecking_context)
	-- If this is strict, simply return it inside a literal, since no substitution is necessary no matter what it is.
	if val:is_strict() then
		return typed_term.literal(val:unwrap_strict())
	end
	if not val:is_stuck() then
		error("val isn't strict or stuck????????")
	end

	local val = val:unwrap_stuck()
	--if val:is_visibility_type() then -- TODO: this track doesn't work anymore
	--	return mark_track(val.track, typed_term.literal(val:unwrap_strict()))
	if val:is_param_info() then
		-- local visibility = val:unwrap_param_info()
		-- TODO: this needs to be evaluated properly because it contains a value
		return typed_term.literal(val)
	elseif val:is_pi() then
		local param_type, param_info, result_type, result_info = val:unwrap_pi()
		local param_type = substitute_inner(param_type, mappings, context_len, ambient_typechecking_context)
		local param_info = substitute_inner(param_info, mappings, context_len, ambient_typechecking_context)
		local result_type = substitute_inner(result_type, mappings, context_len, ambient_typechecking_context)
		local result_info = substitute_inner(result_info, mappings, context_len, ambient_typechecking_context)
		local res = typed_term.pi(param_type, param_info, result_type, result_info)
		res.original_name = val.original_name
		return res
	elseif val:is_closure() then
		local param_name, code, capture, capture_info, param_info = val:unwrap_closure()

		local capture_sub = substitute_inner(capture, mappings, context_len, ambient_typechecking_context)
		local res = typed_term.lambda(param_name, param_info, code, capture_sub, capture_info, param_info.source)
		return res
	elseif val:is_operative_value() then
		local userdata = val:unwrap_operative_value()
		local userdata = substitute_inner(userdata, mappings, context_len, ambient_typechecking_context)
		local res = typed_term.operative_cons(userdata)
		return res
	elseif val:is_operative_type() then
		local handler, userdata_type = val:unwrap_operative_type()
		local typed_handler = substitute_inner(handler, mappings, context_len, ambient_typechecking_context)
		local typed_userdata_type = substitute_inner(userdata_type, mappings, context_len, ambient_typechecking_context)
		local res = typed_term.operative_type_cons(typed_handler, typed_userdata_type)
		return res
	elseif val:is_tuple_value() then
		local elems = val:unwrap_tuple_value()
		local res = typed_array()
		for _, v in elems:ipairs() do
			res:append(substitute_inner(v, mappings, context_len, ambient_typechecking_context))
		end
		local res = typed_term.tuple_cons(res)
		return res
	elseif val:is_tuple_type() then
		local desc = val:unwrap_tuple_type()
		local desc = substitute_inner(desc, mappings, context_len, ambient_typechecking_context)
		local res = typed_term.tuple_type(desc)
		return res
	elseif val:is_tuple_desc_type() then
		local universe = val:unwrap_tuple_desc_type()
		local typed_universe = substitute_inner(universe, mappings, context_len, ambient_typechecking_context)
		local res = typed_term.tuple_desc_type(typed_universe)
		return res
	elseif val:is_enum_value() then
		local constructor, arg = val:unwrap_enum_value()
		local arg = substitute_inner(arg, mappings, context_len, ambient_typechecking_context)
		local res = typed_term.enum_cons(constructor, arg)
		return res
	elseif val:is_enum_type() then
		local desc = val:unwrap_enum_type()
		local desc_sub = substitute_inner(desc, mappings, context_len, ambient_typechecking_context)
		local res = typed_term.enum_type(desc_sub)
		return res
	elseif val:is_enum_desc_type() then
		local univ = val:unwrap_enum_desc_type()
		local univ_sub = substitute_inner(univ, mappings, context_len, ambient_typechecking_context)
		local res = typed_term.enum_desc_type(univ_sub)
		return res
	elseif val:is_enum_desc_value() then
		local variants = val:unwrap_enum_desc_value()
		---@type MapValue
		local variants_sub = string_typed_map()
		for k, v in variants:pairs() do
			variants_sub:set(k, substitute_inner(v, mappings, context_len, ambient_typechecking_context))
		end
		local res = typed_term.enum_desc_cons(
			variants_sub,
			typed_term.literal(strict_value.enum_desc_value(string_value_map()))
		)
		return res
	elseif val:is_record_value() then
		-- TODO: How to deal with a map?
		error("Records not yet implemented")
	elseif val:is_record_type() then
		local desc = val:unwrap_record_type()
		-- TODO: Handle desc properly, because it's a value.
		error("Records not yet implemented")
	elseif val:is_srel_type() then
		local target = val:unwrap_srel_type()
		local target_sub = substitute_inner(target, mappings, context_len, ambient_typechecking_context)
		local res = typed_term.srel_type(target_sub)
		return res
	elseif val:is_variance_type() then
		local target = val:unwrap_variance_type()
		local target_sub = substitute_inner(target, mappings, context_len, ambient_typechecking_context)
		local res = typed_term.variance_type(target_sub)
		return res
	elseif val:is_object_value() then
		-- TODO: this needs to be evaluated properly because it contains a value
		error("Not yet implemented")
	elseif val:is_object_type() then
		-- local desc = val:unwrap_object_type()
		-- TODO: this needs to be evaluated properly because it contains a value
		error("Not yet implemented")
	elseif val:is_free() then
		local free = val:unwrap_free()
		local lookup, mapping, default_mapping, info
		if free:is_placeholder() then
			lookup, info = free:unwrap_placeholder()
			mapping = typed_term.bound_variable(lookup, info)
		elseif free:is_unique() then
			lookup = free:unwrap_unique()
			default_mapping = typed_term.unique(lookup)
		elseif free:is_metavariable() then
			local mv = free:unwrap_metavariable()

			if not (mv.block_level < typechecker_state.block_level) then
				return typechecker_state:slice_constraints_for(mv, mappings, context_len, ambient_typechecking_context)
			else
				lookup = free:unwrap_metavariable()
				default_mapping = typed_term.metavariable(free:unwrap_metavariable())
			end
		else
			error("substitute_inner NYI free with kind " .. free.kind)
		end

		mapping = mappings[lookup] or mapping or default_mapping
		if mapping then
			return mapping
		end
		error(
			"no valid mapping for "
				.. free:pretty_print(ambient_typechecking_context)
				.. " given lookup ID "
				.. tostring(lookup)
		)
	elseif val:is_tuple_element_access() then
		local subject, index = val:unwrap_tuple_element_access()
		local subject_term =
			substitute_inner(flex_value.stuck(subject), mappings, context_len, ambient_typechecking_context)
		local res = typed_term.tuple_element_access(subject_term, index)
		return res
	elseif val:is_host_unwrap() then
		local boxed = val:unwrap_host_unwrap()
		local res = typed_term.host_unwrap(
			substitute_inner(flex_value.stuck(boxed), mappings, context_len, ambient_typechecking_context)
		)
		return res
	elseif val:is_host_wrap() then
		local to_wrap = val:unwrap_host_wrap()
		local res = typed_term.host_wrap(
			substitute_inner(flex_value.stuck(to_wrap), mappings, context_len, ambient_typechecking_context)
		)
		return res
	elseif val:is_host_unwrap() then
		local to_unwrap = val:unwrap_host_unwrap()
		local res = typed_term.host_unwrap(
			substitute_inner(flex_value.stuck(to_unwrap), mappings, context_len, ambient_typechecking_context)
		)
		return res
	elseif val:is_host_application() then
		local fn, arg = val:unwrap_host_application()
		local res = typed_term.application(
			typed_term.literal(strict_value.host_value(fn)),
			substitute_inner(flex_value.stuck(arg), mappings, context_len, ambient_typechecking_context)
		)
		return res
	elseif val:is_host_tuple() then
		local leading, stuck, trailing = val:unwrap_host_tuple()
		local elems = typed_array()
		-- leading is an array of unwrapped host_values and must already be unwrapped host values
		for _, elem in leading:ipairs() do
			local elem_value = typed_term.literal(strict_value.host_value(elem))
			elems:append(elem_value)
		end
		elems:append(substitute_inner(flex_value.stuck(stuck), mappings, context_len, ambient_typechecking_context))
		for _, elem in trailing:ipairs() do
			elems:append(substitute_inner(elem, mappings, context_len, ambient_typechecking_context))
		end
		-- print("host_tuple_stuck nval", nval)
		local result = typed_term.host_tuple_cons(elems)
		-- print("host_tuple_stuck result", result)
		return result
	elseif val:is_host_if() then
		local subject, consequent, alternate = val:unwrap_host_if()
		local subject = substitute_inner(flex_value.stuck(subject), mappings, context_len, ambient_typechecking_context)
		local consequent = substitute_inner(consequent, mappings, context_len, ambient_typechecking_context)
		local alternate = substitute_inner(alternate, mappings, context_len, ambient_typechecking_context)
		return typed_term.host_if(subject, consequent, alternate)
	elseif val:is_application() then
		local fn, arg = val:unwrap_application()
		local res = typed_term.application(
			substitute_inner(flex_value.stuck(fn), mappings, context_len, ambient_typechecking_context),
			substitute_inner(arg, mappings, context_len, ambient_typechecking_context)
		)
		return res
	elseif val:is_host_function_type() then
		local param_type, result_type, res_info = val:unwrap_host_function_type()
		local param_type = substitute_inner(param_type, mappings, context_len, ambient_typechecking_context)
		local result_type = substitute_inner(result_type, mappings, context_len, ambient_typechecking_context)
		local res_info = substitute_inner(res_info, mappings, context_len, ambient_typechecking_context)
		local res = typed_term.host_function_type(param_type, result_type, res_info)
		return res
	elseif val:is_host_wrapped_type() then
		local type = val:unwrap_host_wrapped_type()
		local type = substitute_inner(type, mappings, context_len, ambient_typechecking_context)
		local res = typed_term.host_wrapped_type(type)
		return res
	elseif val:is_host_user_defined_type() then
		local id, family_args = val:unwrap_host_user_defined_type()
		local res = typed_array()
		for _, v in family_args:ipairs() do
			res:append(substitute_inner(v, mappings, context_len, ambient_typechecking_context))
		end
		local res = typed_term.host_user_defined_type_cons(id, res)
		return res
	elseif val:is_host_tuple_type() then
		local desc = val:unwrap_host_tuple_type()
		local desc = substitute_inner(desc, mappings, context_len, ambient_typechecking_context)
		local res = typed_term.host_tuple_type(desc)
		return res
	elseif val:is_range() then
		local lower_bounds, upper_bounds, relation = val:unwrap_range()
		local sub_lower_bounds = typed_array()
		local sub_upper_bounds = typed_array()
		for _, v in lower_bounds:ipairs() do
			local sub = substitute_inner(v, mappings, context_len, ambient_typechecking_context)
			sub_lower_bounds:append(sub)
		end
		for _, v in upper_bounds:ipairs() do
			local sub = substitute_inner(v, mappings, context_len, ambient_typechecking_context)
			sub_upper_bounds:append(sub)
		end
		local sub_relation = substitute_inner(relation, mappings, context_len, ambient_typechecking_context)
		local res = typed_term.range(sub_lower_bounds, sub_upper_bounds, sub_relation)
		return res
	elseif val:is_singleton() then
		local supertype, val = val:unwrap_singleton()
		local supertype_tm = substitute_inner(supertype, mappings, context_len, ambient_typechecking_context)
		local val_tm = substitute_inner(val, mappings, context_len, ambient_typechecking_context)
		local res = typed_term.singleton(supertype_tm, val_tm)
		return res
	elseif val:is_union_type() then
		local a, b = val:unwrap_union_type()
		local res = typed_term.union_type(
			substitute_inner(a, mappings, context_len, ambient_typechecking_context),
			substitute_inner(b, mappings, context_len, ambient_typechecking_context)
		)
		return res
	elseif val:is_intersection_type() then
		local a, b = val:unwrap_intersection_type()
		local res = typed_term.intersection_type(
			substitute_inner(a, mappings, context_len, ambient_typechecking_context),
			substitute_inner(b, mappings, context_len, ambient_typechecking_context)
		)
		return res
	elseif val:is_program_type() then
		local effect, res = val:unwrap_program_type()
		local res = typed_term.program_type(
			substitute_inner(effect, mappings, context_len, ambient_typechecking_context),
			substitute_inner(res, mappings, context_len, ambient_typechecking_context)
		)
		return res
	elseif val:is_effect_row_extend() then
		local row, rest = val:unwrap_effect_row_extend()
		local res = typed_term.effect_row_resolve(
			row,
			substitute_inner(rest, mappings, context_len, ambient_typechecking_context)
		)
		return res
	else
		error("Unhandled value kind in substitute_inner: " .. val.kind)
	end
end

local recurse_count = 0
---@param val flex_value an alicorn value
---@param mappings {[integer]: typed} the placeholder we are trying to get rid of by substituting
---@param context_len integer number of bindings in the runtime context already used - needed for closures
---@param ambient_typechecking_context TypecheckingContext
---@return typed r a typed term
function substitute_inner(val, mappings, context_len, ambient_typechecking_context)
	local tracked = val.track ~= nil
	if tracked then
		print(string.rep("·", recurse_count) .. "SUB: " .. tostring(val))
	end

	verify_placeholder_lite(val, ambient_typechecking_context)
	recurse_count = recurse_count + 1
	local r = substitute_inner_impl(val, mappings, context_len, ambient_typechecking_context)
	recurse_count = recurse_count - 1
	verify_placeholder_lite(r, ambient_typechecking_context)

	if tracked then
		print(string.rep("·", recurse_count) .. " → " .. tostring(r))
		r.track = {}
	end
	return r
end

--for substituting a single var at index
---@param val flex_value
---@param debuginfo var_debug
---@param index integer
---@param param_name string?
---@param ctx FlexRuntimeContext
---@param ambient_typechecking_context TypecheckingContext
---@return flex_value
function substitute_type_variables(val, debuginfo, index, param_name, ctx, ambient_typechecking_context)
	param_name = param_name and "#sub-" .. param_name or "#sub-param"
	--print("value before substituting (val): (value term follows)")
	--print(val)
	local mappings = {
		[index] = typed_term.bound_variable(index, debuginfo),
	}
	local size = ambient_typechecking_context.bindings:len()
	for i = 1, size do
		local _, info = ambient_typechecking_context.runtime_context:get(i)
		mappings[i] = typed.bound_variable(i, info)
	end
	local substituted = substitute_inner(val, mappings, index, ambient_typechecking_context)
	--print("typed term after substitution (substituted): (typed term follows)")
	--print(substituted:pretty_print(typechecking_context))
	return U.notail(flex_value.closure(param_name, substituted, ctx, debuginfo))
end

---@param val flex_value
---@param typechecking_context TypecheckingContext
---@param hidden integer?
---@return typed
local function substitute_placeholders_identity(val, typechecking_context, hidden)
	local mappings = {}
	local size = typechecking_context.bindings:len()
	for i = 1, size do
		local _, info = typechecking_context.runtime_context:get(i)
		mappings[i] = typed.bound_variable(i, info)
	end
	local r = substitute_inner(val, mappings, size + (hidden or 0), typechecking_context)
	return r
end

---@param val flex_value
---@return boolean
local function is_type_of_types(val)
	return val:is_star() or val:is_prop() or val:is_host_type_type()
end

local check_concrete
-- indexed by kind x kind
---@type {[string] : {[string] : value_comparer}}
local concrete_comparers = {}

---collapse accessor paths into concrete type bounds
---@param ctx TypecheckingContext
---@param typ flex_value
---@param cause any
---@return TypecheckingContext, flex_value
local function revealing(ctx, typ, cause)
	if not typ:is_stuck() then
		return ctx, typ
	end

	local nv = typ:unwrap_stuck()

	if nv:is_tuple_element_access() then
		error("nyi")
		local subject, elem = nv:unwrap_tuple_element_access()
		if subject:is_free() then
			local var = subject:unwrap_free()
			if var:is_placeholder() then
				local idx, dbg = var:unwrap_placeholder()
				local inner = ctx:get_type(idx)
				local inner_bound = flex_value.tuple_type(typechecker_state:metavariable(ctx, false):as_flex())
				print("found inner", inner)
				error "FINISH THIS"
			end
		else
			error("NYI, revealing a tuple access that isn't on a variable" .. subject:pretty_print(ctx))
		end
	end
	error(
		"NYI, revealing something that isn't a tuple access "
			.. nv:pretty_print(ctx)
			.. "\ncontext: "
			.. ctx:format_names()
			.. "\ncaused by: "
			.. tostring(cause)
	)
end

---take apart a symbolic tuple value to produce a (simplified? hopefully?) prefix suitable for use in upcasting and downcasting
---@param subject flex_value
---@param idx integer
---@return flex_value
local function tuple_slice(subject, idx)
	if subject:is_stuck() then
		local nv = subject:unwrap_stuck()
		if nv:is_free() then
			return subject
		end
	end
	error "NYI any other tuple plsfix" --FIXME --TODO
end

---extract a specified element type from a given tuple desc
---@param subject flex_value
---@param desc flex_value
---@param idx integer
---@return flex_value
local function extract_desc_nth(subject, desc, idx)
	local slices = {}
	repeat
		local variant, args = desc:unwrap_enum_value()
		local done = false
		if variant == terms.DescCons.empty then
			done = true
		elseif variant == terms.DescCons.cons then
			local elements = args:unwrap_host_tuple_value()
			local pfx, elem = elements:unpack()
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
---@param typ flex_value
---@return TypecheckingContext, flex_value
local function upcast(ctx, typ, cause)
	if not typ:is_stuck() then
		return ctx, typ
	end

	local nv = typ:unwrap_stuck()

	if nv:is_tuple_element_access() then
		local subject, elem = nv:unwrap_tuple_element_access()
		if subject:is_free() then
			local var = subject:unwrap_free()
			if var:is_placeholder() then
				local idx, dbg = var:unwrap_placeholder()
				local inner = ctx:get_type(idx)
				--local inner_bound = flex_value.tuple_type(typechecker_state:metavariable(ctx, false):as_flex())
				local context2, boundstype = revealing(ctx, inner, cause)
				--TODO: speculate for bottom
				--TODO: speculate on tuple type and reformulate extraction in terms of constraining
				if boundstype:is_tuple_type() then
					local desc = boundstype:unwrap_tuple_type()
					local member = extract_desc_nth(flex_value.stuck(subject), desc, elem)
					--TODO: level srel? speculate on member types?
					if member:is_star() then
						local level, depth = member:unwrap_star()
						if depth > 0 then
							return ctx, flex_value.star(level - 1, depth - 1)
						end
					end
				end
			end
		end
	end
	error "NYI upcast something or other"
end

---@alias value_comparer fun(l_ctx: TypecheckingContext, a: flex_value, r_ctx: TypecheckingContext, b: flex_value, cause: constraintcause): boolean, ConstraintError?

---@param ka string
---@param kb string
---@param comparer value_comparer
local function add_comparer(ka, kb, comparer)
	concrete_comparers[ka] = concrete_comparers[ka] or {}
	concrete_comparers[ka][kb] = comparer
end

---@type value_comparer
local function always_fits_comparer(l_ctx, a, r_ctx, b, cause)
	return true
end

-- host types
add_comparer("flex_value.host_number_type", "flex_value.host_number_type", always_fits_comparer)
add_comparer("flex_value.host_string_type", "flex_value.host_string_type", always_fits_comparer)
add_comparer("flex_value.host_bool_type", "flex_value.host_bool_type", always_fits_comparer)
add_comparer("flex_value.host_user_defined_type", "flex_value.host_user_defined_type", always_fits_comparer)

-- types of types
add_comparer("flex_value.host_type_type", "flex_value.host_type_type", always_fits_comparer)
add_comparer("flex_value.tuple_type", "flex_value.tuple_type", function(l_ctx, a, r_ctx, b, cause)
	local desc_a = a:unwrap_tuple_type()
	local desc_b = b:unwrap_tuple_type()
	typechecker_state:queue_constrain(
		l_ctx,
		desc_a,
		TupleDescRelation,
		r_ctx,
		desc_b,
		nestcause("tuple type", cause, desc_a, desc_b, l_ctx, r_ctx)
	)
	return true
end)
add_comparer("flex_value.host_tuple_type", "flex_value.host_tuple_type", function(l_ctx, a, r_ctx, b, cause)
	local desc_a = a:unwrap_host_tuple_type()
	local desc_b = b:unwrap_host_tuple_type()
	typechecker_state:queue_constrain(
		l_ctx,
		desc_a,
		TupleDescRelation,
		r_ctx,
		desc_b,
		nestcause("host tuple type", cause, desc_a, desc_b, l_ctx, r_ctx)
	)
	return true
end)
add_comparer("flex_value.enum_desc_type", "flex_value.enum_desc_type", function(l_ctx, a, r_ctx, b, cause)
	local a_univ = a:unwrap_enum_desc_type()
	local b_univ = b:unwrap_enum_desc_type()
	typechecker_state:queue_subtype(
		l_ctx,
		a_univ,
		r_ctx,
		b_univ,
		nestcause("enum desc universe covariance", cause, a_univ, b_univ, l_ctx, r_ctx)
	)
	return true
end)
add_comparer("flex_value.enum_type", "flex_value.enum_type", function(l_ctx, a, r_ctx, b, cause)
	local a_desc = a:unwrap_enum_type()
	local b_desc = b:unwrap_enum_type()
	typechecker_state:queue_constrain(
		l_ctx,
		a_desc,
		EnumDescRelation,
		r_ctx,
		b_desc,
		nestcause("enum type description", cause, a_desc, b_desc, l_ctx, r_ctx)
	)
	return true
end)
add_comparer("flex_value.enum_type", "flex_value.tuple_desc_type", function(l_ctx, a, r_ctx, b, cause)
	local a_desc = a:unwrap_enum_type()
	local b_univ = b:unwrap_tuple_desc_type()
	local construction_variants = string_value_map()
	-- The empty variant has no arguments
	construction_variants:set(
		terms.DescCons.empty,
		flex_value.tuple_type(flex_value.enum_value(terms.DescCons.empty, flex_value.tuple_value(flex_value_array())))
	)
	local arg_name = terms.var_debug("#arg" .. tostring(#r_ctx + 1), U.anchor_here())
	local univ_dbg = terms.var_debug("#univ", U.anchor_here())
	local prefix_desc_dbg = terms.var_debug("#prefix-desc", U.anchor_here())
	-- The cons variant takes a prefix description and a next element, represented as a function from the prefix tuple to a type in the specified universe
	construction_variants:set(
		terms.DescCons.cons,
		flex_value.tuple_type(
			flex_value.enum_value(
				terms.DescCons.cons,
				flex_value.tuple_value(
					flex_value_array(
						flex_value.enum_value(
							terms.DescCons.cons,
							flex_value.tuple_value(
								flex_value_array(
									flex_value.enum_value(
										terms.DescCons.empty,
										flex_value.tuple_value(flex_value_array())
									),
									flex_value.closure(
										"#prefix",
										substitute_placeholders_identity(b, r_ctx, 1),
										r_ctx.runtime_context,
										terms.var_debug("#prefix", U.anchor_here())
									)
								)
							)
						),
						flex_value.closure(
							"#prefix",
							typed_term.tuple_elim(
								string_array("prefix-desc"),
								debug_array(prefix_desc_dbg),
								typed_term.bound_variable(#r_ctx + 2, arg_name),
								1,
								typed_term.pi(
									typed_term.tuple_type(typed_term.bound_variable(#r_ctx + 3, prefix_desc_dbg)),
									typed.literal(
										strict_value.param_info(strict_value.visibility(terms.visibility.explicit))
									),
									typed.lambda(
										arg_name.name,
										arg_name,
										typed_term.bound_variable(#r_ctx + 1, univ_dbg),
										U.anchor_here()
									),
									typed.literal(strict_value.result_info(terms.result_info(terms.purity.pure)))
								)
							),
							r_ctx.runtime_context:append(b_univ, "b_univ", univ_dbg),
							arg_name
						)
					)
				)
			)
		)
	)
	local enum_desc_val = flex_value.enum_desc_value(construction_variants)
	typechecker_state:queue_constrain(
		l_ctx,
		a_desc,
		EnumDescRelation,
		r_ctx,
		enum_desc_val,
		nestcause("use enum construction as tuple desc", cause, a_desc, enum_desc_val, l_ctx, r_ctx)
	)
	return true
end)
add_comparer("flex_value.tuple_desc_type", "flex_value.enum_type", function(l_ctx, a, r_ctx, b, cause)
	local a_univ = a:unwrap_tuple_desc_type()
	local b_desc = b:unwrap_enum_type()
	local construction_variants = string_value_map()
	-- The empty variant has no arguments
	construction_variants:set(
		terms.DescCons.empty,
		flex_value.tuple_type(flex_value.enum_value(terms.DescCons.empty, flex_value.tuple_value(flex_value_array())))
	)
	-- The cons variant takes a prefix description and a next element, represented as a function from the prefix tuple to a type in the specified universe
	construction_variants:set(
		terms.DescCons.cons,
		flex_value.tuple_type(
			flex_value.enum_value(
				terms.DescCons.cons,
				flex_value.tuple_value(
					flex_value_array(
						flex_value.enum_value(
							terms.DescCons.cons,
							flex_value.tuple_value(
								flex_value_array(
									flex_value.enum_value(
										terms.DescCons.empty,
										flex_value.tuple_value(flex_value_array())
									),
									flex_value.closure(
										"#prefix",
										typed_term.literal(a),
										r_ctx.runtime_context,
										terms.var_debug("", U.anchor_here())
									)
								)
							)
						),
						flex_value.closure(
							"#prefix",
							typed_term.tuple_elim(
								string_array("prefix-desc"),
								debug_array(terms.var_debug("prefix-desc", U.anchor_here())),
								typed_term.bound_variable(#r_ctx + 2, terms.var_debug("", U.anchor_here())),
								1,
								typed_term.pi(
									typed_term.tuple_type(
										typed_term.bound_variable(#r_ctx + 3, terms.var_debug("", U.anchor_here()))
									),
									typed.literal(
										strict_value.param_info(strict_value.visibility(terms.visibility.explicit))
									),
									typed.lambda(
										"#arg" .. tostring(#r_ctx + 1),
										terms.var_debug("", U.anchor_here()),
										typed_term.bound_variable(#r_ctx + 1, terms.var_debug("", U.anchor_here())),
										U.anchor_here()
									),
									typed.literal(strict_value.result_info(terms.result_info(terms.purity.pure)))
								)
							),
							r_ctx.runtime_context:append(a_univ, "a_univ", terms.var_debug("", U.anchor_here())),
							terms.var_debug("", U.anchor_here())
						)
					)
				)
			)
		)
	)
	local enum_desc_val = flex_value.enum_desc_value(construction_variants)
	typechecker_state:queue_constrain(
		l_ctx,
		enum_desc_val,
		EnumDescRelation,
		r_ctx,
		b_desc,
		nestcause("use tuple description as enum", cause, enum_desc_val, b_desc, l_ctx, r_ctx)
	)
	return true
end)
add_comparer("flex_value.pi", "flex_value.pi", function(l_ctx, a, r_ctx, b, cause)
	if a == b then
		return true
	end

	local a_param_type, a_param_info, a_result_type, a_result_info = a:unwrap_pi()
	local b_param_type, b_param_info, b_result_type, b_result_info = b:unwrap_pi()

	local a_vis = a_param_info:unwrap_param_info():unwrap_visibility()
	local b_vis = b_param_info:unwrap_param_info():unwrap_visibility()
	if a_vis ~= b_vis and not a_vis:is_implicit() then
		return false, ConstraintError.new("pi param_info: ", a_vis, l_ctx, "~=", b_vis, r_ctx)
	end

	local a_purity = a_result_info:unwrap_result_info():unwrap_result_info()
	local b_purity = b_result_info:unwrap_result_info():unwrap_result_info()
	if a_purity ~= b_purity then
		return false, ConstraintError.new("pi result_info: ", a_purity, l_ctx, "~=", b_purity, r_ctx)
	end

	typechecker_state:queue_subtype(
		r_ctx,
		b_param_type,
		l_ctx,
		a_param_type,
		nestcause("pi function parameters", cause, b_param_type, a_param_type, r_ctx, l_ctx)
	)
	--local unique_placeholder = flex_value.stuck(terms.stuck_value.free(terms.free.unique({})))
	--local a_res = apply_value(a_result_type, unique_placeholder)
	--local b_res = apply_value(b_result_type, unique_placeholder)
	--typechecker_state:queue_constrain(a_res, FunctionRelation(UniverseOmegaRelation), b_res, "pi function results")

	--TODO implement the SA-ALL rule which is slightly more powerful than this rule
	typechecker_state:queue_constrain(
		l_ctx,
		a_result_type,
		FunctionRelation(UniverseOmegaRelation),
		r_ctx,
		b_result_type,
		nestcause("pi function results", cause, a_result_type, b_result_type, l_ctx, r_ctx)
	)

	return true
end)
add_comparer("flex_value.host_function_type", "flex_value.host_function_type", function(l_ctx, a, r_ctx, b, cause)
	if a == b then
		return true
	end

	local a_param_type, a_result_type, a_result_info = a:unwrap_host_function_type()
	local b_param_type, b_result_type, b_result_info = b:unwrap_host_function_type()

	local a_purity = a_result_info:unwrap_result_info():unwrap_result_info()
	local b_purity = b_result_info:unwrap_result_info():unwrap_result_info()
	if a_purity ~= b_purity then
		return false, ConstraintError.new("host function result_info: ", a_purity, l_ctx, "~=", b_purity, r_ctx)
	end

	typechecker_state:queue_subtype(
		r_ctx,
		b_param_type,
		l_ctx,
		a_param_type,
		nestcause("host function parameters", cause, b_param_type, a_param_type, r_ctx, l_ctx)
	)
	--local unique_placeholder = flex_value.stuck(terms.stuck_value.free(terms.free.unique({})))
	--local a_res = apply_value(a_result_type, unique_placeholder)
	--local b_res = apply_value(b_result_type, unique_placeholder)
	--typechecker_state:queue_constrain(b_res, FunctionRelation(UniverseOmegaRelation), a_res, "host function parameters")

	--TODO implement the SA-ALL rule which is slightly more powerful than this rule
	typechecker_state:queue_constrain(
		l_ctx,
		a_result_type,
		FunctionRelation(UniverseOmegaRelation),
		r_ctx,
		b_result_type,
		nestcause("host function results", cause, a_result_type, b_result_type, l_ctx, r_ctx)
	)
	return true
end)

---@type {[table] : SubtypeRelation}
local host_srel_map = {}
add_comparer(
	"flex_value.host_user_defined_type",
	"flex_value.host_user_defined_type",
	function(l_ctx, a, r_ctx, b, cause)
		local a_id, a_args = a:unwrap_host_user_defined_type()
		local b_id, b_args = b:unwrap_host_user_defined_type()

		if not a_id == b_id then
			error(
				ConstraintError(
					"ids do not match in host user defined types: " .. a_id.name .. " ",
					a_id,
					l_ctx,
					" ~= " .. b_id.name .. " ",
					b_id,
					r_ctx
				)
			)
		end
		if not host_srel_map[a_id] then
			error("No variance specified for user defined host type " .. a_id.name)
		end
		local a_value, b_value = flex_value.tuple_value(a_args), flex_value.tuple_value(b_args)
		return apply_value(
				flex_value.strict(host_srel_map[a_id].constrain),
				flex_value.tuple_value(
					flex_value_array(
						flex_value.host_value(l_ctx),
						flex_value.host_value(a_value),
						flex_value.host_value(r_ctx),
						flex_value.host_value(b_value),
						flex_value.host_value(
							nestcause(
								"host_user_defined_type compared against host_user_defined_type",
								cause,
								a_value,
								b_value,
								l_ctx,
								r_ctx
							)
						)
					)
				),
				l_ctx
			)
			:unwrap_host_tuple_value()
			:unpack()
	end
)

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

add_comparer("flex_value.srel_type", "flex_value.srel_type", function(l_ctx, a, r_ctx, b, cause)
	local a_target = a:unwrap_srel_type()
	local b_target = b:unwrap_srel_type()
	typechecker_state:queue_subtype(
		l_ctx,
		a_target,
		r_ctx,
		b_target,
		nestcause("srel target", cause, a_target, b_target, l_ctx, r_ctx)
	)
	return true
end)

add_comparer("flex_value.variance_type", "flex_value.variance_type", function(l_ctx, a, r_ctx, b, cause)
	local a_target = a:unwrap_variance_type()
	local b_target = b:unwrap_variance_type()
	typechecker_state:queue_subtype(
		r_ctx,
		b_target,
		l_ctx,
		a_target,
		nestcause("variance target", cause, b_target, a_target, r_ctx, l_ctx)
	)
	return true
end)

add_comparer("flex_value.host_type_type", "flex_value.star", function(l_ctx, a, r_ctx, b, cause)
	local level, depth = b:unwrap_star()
	if depth == 0 then
		return true
	else
		return false,
			ConstraintError.new(
				"host_type_type does not contain types (i.e. does not fit in stars deeper than 0)",
				a,
				l_ctx,
				"does not fit",
				b,
				r_ctx,
				cause
			)
	end
end)

add_comparer("flex_value.star", "flex_value.star", function(l_ctx, a, r_ctx, b, cause)
	local a_level, a_depth = a:unwrap_star()
	local b_level, b_depth = b:unwrap_star()
	if a_level > b_level then
		print("star-comparer error:")
		print("a level:", a_level)
		print("b level:", b_level)
		return false, ConstraintError.new("a.level > b.level", a, l_ctx, ">", b, r_ctx, cause)
	end
	if a_depth < b_depth then
		print("star-comparer error:")
		print("a depth:", a_depth)
		print("b depth:", b_depth)
		return false, ConstraintError.new("a.depth < b.depth", a, l_ctx, "<", b, r_ctx, cause)
	end
	return true
end)

add_comparer("flex_value.host_wrapped_type", "flex_value.host_wrapped_type", function(l_ctx, a, r_ctx, b, cause)
	local a_type, b_type = a:unwrap_host_wrapped_type(), b:unwrap_host_wrapped_type()
	typechecker_state:queue_subtype(
		l_ctx,
		a_type,
		r_ctx,
		b_type,
		nestcause("wrapped type target", cause, a_type, b_type, l_ctx, r_ctx)
	)
	--U.tag("check_concrete", { ua, ub }, check_concrete, ua, ub)
	return true
end)

add_comparer("flex_value.singleton", "flex_value.singleton", function(l_ctx, a, r_ctx, b, cause)
	local a_supertype, a_value = a:unwrap_singleton()
	local b_supertype, b_value = b:unwrap_singleton()
	typechecker_state:queue_subtype(
		l_ctx,
		a_supertype,
		r_ctx,
		b_supertype,
		nestcause("singleton supertypes", cause, a_supertype, b_supertype, l_ctx, r_ctx)
	)

	if a_value == b_value then
		return true
	else
		return false, ConstraintError.new("singletons", a, l_ctx, "~=", b, r_ctx, cause)
	end
end)

add_comparer("flex_value.tuple_desc_type", "flex_value.tuple_desc_type", function(l_ctx, a, r_ctx, b, cause)
	local a_universe = a:unwrap_tuple_desc_type()
	local b_universe = b:unwrap_tuple_desc_type()
	typechecker_state:queue_subtype(
		l_ctx,
		a_universe,
		r_ctx,
		b_universe,
		nestcause("tuple_desc_type universes", cause, a_universe, b_universe, l_ctx, r_ctx)
	)
	return true
end)

add_comparer("flex_value.program_type", "flex_value.program_type", function(l_ctx, a, r_ctx, b, cause)
	local a_eff, a_base = a:unwrap_program_type()
	local b_eff, b_base = b:unwrap_program_type()
	typechecker_state:queue_subtype(
		l_ctx,
		a_base,
		r_ctx,
		b_base,
		terms.constraintcause.primitive("program result", U.anchor_here())
	)
	typechecker_state:queue_constrain(
		l_ctx,
		a_eff,
		EffectRowRelation,
		r_ctx,
		b_eff,
		nestcause("program effects", cause, a_eff, b_eff, l_ctx, r_ctx)
	)
	return true
end)

add_comparer("flex_value.effect_row_type", "flex_value.effect_row_type", function(l_ctx, a, r_ctx, b, cause)
	return true
end)
add_comparer("flex_value.effect_type", "flex_value.effect_type", function(l_ctx, a, r_ctx, b, cause)
	return true
end)

---@param kind string
---@return string
function unify_kind(kind)
	local r, _ = string.gsub(kind, "([^%.]+)%.([^%.]+)", "flex_value.%2")
	return r
end

--- Compares concrete type-heads, and induces any necessary constraints on their components.
---@param l_ctx TypecheckingContext
---@param val flex_value
---@param r_ctx TypecheckingContext
---@param use flex_value
---@param cause constraintcause
---@return boolean
---@return ConstraintError? error
function check_concrete(l_ctx, val, r_ctx, use, cause)
	-- Note: in general, val must be a more specific type than use
	if val == nil then
		error("nil value passed into check_concrete!")
	end
	if use == nil then
		error("nil usage passed into check_concrete!")
	end

	local val_kind
	local use_kind
	if val:is_strict() then
		val_kind = unify_kind(val:unwrap_strict().kind)
	end
	if val:is_stuck() then
		val_kind = unify_kind(val:unwrap_stuck().kind)
	end
	if use:is_strict() then
		use_kind = unify_kind(use:unwrap_strict().kind)
	end
	if use:is_stuck() then
		use_kind = unify_kind(use:unwrap_stuck().kind)
	end

	local comparer = nil
	if concrete_comparers[val_kind] then
		comparer = (concrete_comparers[val_kind] or {})[use_kind]
	end

	if comparer then
		return comparer(l_ctx, val, r_ctx, use, cause)
	end

	if val:is_singleton() and not use:is_singleton() then
		local val_supertype, _ = val:unwrap_singleton()
		typechecker_state:queue_subtype(
			l_ctx,
			val_supertype,
			r_ctx,
			use,
			nestcause("singleton subtype", cause, val_supertype, use, l_ctx, r_ctx)
		)
		return true
	end

	if val:is_union_type() then
		local val_a, val_b = val:unwrap_union_type()
		typechecker_state:queue_subtype(
			l_ctx,
			val_a,
			r_ctx,
			use,
			nestcause("union dissasembly", cause, val_a, use, l_ctx, r_ctx)
		)
		typechecker_state:queue_subtype(
			l_ctx,
			val_b,
			r_ctx,
			use,
			nestcause("union dissasembly", cause, val_b, use, l_ctx, r_ctx)
		)
		return true
	end

	if use:is_intersection_type() then
		local use_a, use_b = use:unwrap_intersection_type()
		typechecker_state:queue_subtype(
			l_ctx,
			val,
			r_ctx,
			use_a,
			nestcause("intersection dissasembly", cause, val, use_a, l_ctx, r_ctx)
		)
		typechecker_state:queue_subtype(
			l_ctx,
			val,
			r_ctx,
			use_b,
			nestcause("intersection dissasembly", cause, val, use_b, l_ctx, r_ctx)
		)
		return true
	end

	if val:is_stuck() then
		if use:is_stuck() then
			if val == use then
				return true
			end
		end
		local val_stuck = val:unwrap_stuck()
		if val_stuck:is_tuple_element_access() then
			local inner_ctx, bound = upcast(l_ctx, val, cause)
			typechecker_state:queue_subtype(
				inner_ctx,
				bound,
				r_ctx,
				use,
				nestcause("concrete upcast", cause, bound, use, inner_ctx, r_ctx)
			)
			return true
		end
		if val_stuck:is_free() then
			local free = val_stuck:unwrap_free()
			if free:is_placeholder() then
				local idx, dbg = free:unwrap_placeholder()
				local inner = l_ctx:get_type(idx)
				--local inner_bound = flex_value.tuple_type(typechecker_state:metavariable(ctx, false):as_flex())
				local inner_ctx, bounds_type = revealing(l_ctx, inner)

				typechecker_state:queue_subtype(
					inner_ctx,
					bounds_type,
					r_ctx,
					use,
					nestcause("concrete reveal placeholder", cause, bounds_type, use, inner_ctx, r_ctx)
				)
				return true
			end
		end
	end

	if use:is_stuck() then
		--TODO: downcast and test

		if val:is_stuck() then
			diff:get(flex_value).diff(val, use)
			return false,
				ConstraintError.new(
					"both values are neutral, but they aren't equal: ",
					val,
					l_ctx,
					"~=",
					use,
					r_ctx,
					cause
				)
		end
	end

	if not concrete_comparers[val_kind] then
		error(
			ConstraintError.new(
				"No valid concrete type comparer found for value " .. val_kind,
				val,
				l_ctx,
				nil,
				nil,
				nil,
				cause
			)
		)
	end

	if not comparer then
		--print("kind:", valkind, " use:", usekind)
		return false,
			ConstraintError.new(
				"no valid concrete comparer between value " .. val_kind .. " and usage " .. use_kind,
				val,
				l_ctx,
				"compared against",
				use,
				r_ctx,
				cause
			)
	end

	error("unreachable???")
end

---@param enum_val flex_value
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
	error "unknown enum constructor for flex_value.tuple_type's enum_value, should not be reachable"
end

---@overload fun(checkable_term : checkable, typechecking_context : TypecheckingContext, goal_type : flex_value) : boolean, string
---@param checkable_term checkable
---@param typechecking_context TypecheckingContext
---@param goal_type flex_value
---@return boolean, ArrayValue, typed
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
	if flex_value.value_check(goal_type) ~= true then
		print("goal_type", goal_type)
		error(
			"check, goal_type: expected a goal type (as an alicorn flex_value, did you use a strict or stuck value instead?)"
		)
	end

	if checkable_term:is_inferrable() then
		local inferrable_term = checkable_term:unwrap_inferrable()
		local ok, inferred_type, inferred_usages, typed_term = infer(inferrable_term, typechecking_context)
		if not ok then
			---@cast inferred_type -flex_value
			return false, inferred_type
		end

		-- TODO: unify!!!! (instead of the below equality check)
		if inferred_type ~= goal_type then
			-- FIXME: needs context to avoid bugs where inferred and goal are the same neutral structurally
			-- but come from different context thus are different
			-- but erroneously compare equal
			local ok, err = typechecker_state:flow(
				inferred_type,
				typechecking_context,
				goal_type,
				typechecking_context,
				terms.constraintcause.primitive("inferrable", U.anchor_here())
			)
			if not ok then
				---@cast err -nil
				return false, err
			end
		end

		return true, inferred_usages, typed_term
	elseif checkable_term:is_tuple_cons() then
		local elements, info = checkable_term:unwrap_tuple_cons()
		local usages = usage_array()
		local new_elements = typed_array()
		local desc = terms.empty

		for i, v in elements:ipairs() do
			local el_type_metavar = typechecker_state:metavariable(typechecking_context)
			local el_type = el_type_metavar:as_flex()
			local ok, el_usages, el_term = check(v, typechecking_context, el_type)
			if not ok then
				return false, el_usages
			end

			add_arrays(usages, el_usages)
			new_elements:append(el_term)

			local el_val = evaluate(el_term, typechecking_context.runtime_context, typechecking_context)

			desc = terms.cons(
				desc,
				flex_value.closure(
					"#check-tuple-cons-param",
					substitute_placeholders_identity(flex_value.singleton(el_type, el_val), typechecking_context, 1),
					typechecking_context.runtime_context,
					info[i]
				)
			)
		end

		local ok, err = typechecker_state:flow(
			flex_value.tuple_type(desc),
			typechecking_context,
			goal_type,
			typechecking_context,
			terms.constraintcause.primitive("checkable_term:is_tuple_cons", U.anchor_here())
		)
		if not ok then
			return false, err
		end

		return true, usages, typed_term.tuple_cons(new_elements)
	elseif checkable_term:is_host_tuple_cons() then
		local elements, info = checkable_term:unwrap_host_tuple_cons()
		local usages = usage_array()
		local new_elements = typed_array()
		local desc = terms.empty

		for i, v in elements:ipairs() do
			local el_type_metavar = typechecker_state:metavariable(typechecking_context)
			local el_type = el_type_metavar:as_flex()
			local ok, el_usages, el_term = check(v, typechecking_context, el_type)
			if not ok then
				return false, el_usages
			end

			add_arrays(usages, el_usages)
			new_elements:append(el_term)

			local el_val = evaluate(el_term, typechecking_context.runtime_context, typechecking_context)

			desc = terms.cons(
				desc,
				flex_value.closure(
					"#check-tuple-cons-param",
					substitute_placeholders_identity(flex_value.singleton(el_type, el_val), typechecking_context, 1),
					typechecking_context.runtime_context,
					info[i]
				)
			)
		end

		local ok, err = typechecker_state:flow(
			flex_value.host_tuple_type(desc),
			typechecking_context,
			goal_type,
			typechecking_context,
			terms.constraintcause.primitive("checkable_term:is_host_tuple_cons", U.anchor_here())
		)
		if not ok then
			return false, err
		end

		return true, usages, typed_term.host_tuple_cons(new_elements)
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
---@param f flex_value
---@param arg flex_value
---@param ambient_typechecking_context TypecheckingContext
---@return flex_value
function apply_value(f, arg, ambient_typechecking_context)
	if flex_value.value_check(f) ~= true then
		error("apply_value, f: expected an alicorn flex_value (did you forget to wrap a strict value in flex_value?)")
	end
	if flex_value.value_check(arg) ~= true then
		error("apply_value, arg: expected an alicorn flex_value (did you forget to wrap a strict value in flex_value?)")
	end

	if f:is_closure() then
		local param_name, code, capture, capture_dbg, debuginfo = f:unwrap_closure()
		--return U.notail(U.tag("evaluate", { code = code }, evaluate, code, capture:append(arg)))
		local ctx = terms.flex_runtime_context()
		ctx = ctx:append(capture, "#capture", capture_dbg)
		ctx = ctx:append(arg, param_name, debuginfo)
		return evaluate(code, ctx, ambient_typechecking_context)
	elseif f:is_stuck() then
		return flex_value.stuck(stuck_value.application(f:unwrap_stuck(), arg))
	elseif f:is_host_value() then
		local host_func_impl = f:unwrap_host_value()
		if host_func_impl == nil then
			error "expected to get a function but found nil, did you forget to return the function from an intrinsic"
		end
		if arg:is_host_tuple_value() then
			local arg_elements = arg:unwrap_host_tuple_value()
			return flex_value.host_tuple_value(host_array(host_func_impl(arg_elements:unpack())))
		elseif arg:is_stuck() then
			return flex_value.stuck(stuck_value.host_application(host_func_impl, arg:unwrap_stuck()))
		else
			error("apply_value, is_host_value, arg: expected a host tuple argument")
		end
	else
		error(
			ConstraintError.new(
				"apply_value, f: expected a function/closure, but got ",
				f,
				ambient_typechecking_context
			)
		)
	end

	error("unreachable!?")
end

---@param subject flex_value
---@param index integer
---@return flex_value
local function index_tuple_value(subject, index)
	if flex_value.value_check(subject) ~= true then
		error(
			"index_tuple_value, subject: expected an alicorn flex_value (did you forget to wrap a strict value in flex_value?)"
		)
	end

	if subject:is_tuple_value() then
		local elems = subject:unwrap_tuple_value()
		return elems[index]
	elseif subject:is_host_tuple_value() then
		local elems = subject:unwrap_host_tuple_value()
		return flex_value.host_value(elems[index])
	elseif subject:is_stuck() then
		local inner = subject:unwrap_stuck()
		if inner:is_host_tuple() then
			local leading, stuck_elem, trailing = inner:unwrap_host_tuple()
			if leading:len() >= index then
				return flex_value.host_value(leading[index])
			elseif leading:len() + 1 == index then
				return flex_value.stuck(stuck_elem)
			elseif leading:len() + 1 + trailing:len() >= index then
				return trailing[index - leading:len() - 1]
			else
				error "tuple index out of bounds"
			end
		end
		return flex_value.stuck(stuck_value.tuple_element_access(inner, index))
	end
	print(index, subject)
	error("Should be unreachable???")
end

local host_tuple_make_prefix_mt = {
	---@param i integer
	---@return flex_value
	__call = function(self, i)
		local prefix_elements = flex_value_array()
		for x = 1, i do
			prefix_elements:append(flex_value.stuck(stuck_value.tuple_element_access(self.subject_stuck_value, x)))
		end
		return flex_value.tuple_value(prefix_elements)
	end,
}
---@param subject_stuck_value stuck_value
---@return fun(i: integer): flex_value
local function host_tuple_make_prefix(subject_stuck_value)
	return setmetatable({ subject_stuck_value = subject_stuck_value }, host_tuple_make_prefix_mt)
end

---@param subject_type flex_value
---@param subject_value flex_value
---@return flex_value desc `subject_type.desc`
---@return fun(i: integer): flex_value make_prefix
local function make_tuple_prefix(subject_type, subject_value)
	local desc, make_prefix
	if subject_type:is_tuple_type() then
		desc = subject_type:unwrap_tuple_type()

		if subject_value:is_tuple_value() then
			local subject_elements = subject_value:unwrap_tuple_value()
			---@param i integer
			---@return flex_value
			function make_prefix(i)
				return flex_value.tuple_value(subject_elements:copy(1, i))
			end
		elseif subject_value:is_stuck() then
			local subject_stuck_value = subject_value:unwrap_stuck()
			---@param i integer
			---@return flex_value
			function make_prefix(i)
				local prefix_elements = flex_value_array()
				for x = 1, i do
					prefix_elements:append(flex_value.stuck(stuck_value.tuple_element_access(subject_stuck_value, x)))
				end
				return flex_value.tuple_value(prefix_elements)
			end
		else
			error(
				ConstraintError.new(
					"make_tuple_prefix, is_tuple_type, subject_value: expected a tuple, instead got ",
					subject_value
				)
			)
		end
	elseif subject_type:is_host_tuple_type() then
		desc = subject_type:unwrap_host_tuple_type()

		if subject_value:is_host_tuple_value() then
			local subject_elements = subject_value:unwrap_host_tuple_value()
			local subject_value_elements = flex_value_array()
			for _, v in subject_elements:ipairs() do
				subject_value_elements:append(flex_value.host_value(v))
			end
			---@param i integer
			---@return flex_value
			function make_prefix(i)
				return flex_value.tuple_type(subject_value_elements:copy(1, i))
			end
		elseif subject_value:is_stuck() then
			-- yes, literally a copy-paste of the stuck case above
			local subject_stuck_value = subject_value:unwrap_stuck()
			make_prefix = host_tuple_make_prefix(subject_stuck_value)
		else
			error(
				ConstraintError.new(
					"make_tuple_prefix, is_host_tuple_type, subject_value: expected a host tuple, instead got ",
					subject_value
				)
			)
		end
	else
		error("make_tuple_prefix, subject_type: expected a term with a tuple type, but got " .. subject_type.kind)
	end

	return desc, make_prefix
end

-- TODO: create a typechecking context append variant that merges two
---@param desc flex_value
---@param make_prefix fun(i: integer): flex_value
---@return flex_value[] tuple_types
---@return integer n_elements
---@return flex_value[] tuple_vals
function make_inner_context(desc, make_prefix)
	-- evaluate the type of the tuple
	local constructor, arg = desc:unwrap_enum_value()
	if constructor == terms.DescCons.empty then
		return flex_value_array(), 0, flex_value_array()
	elseif constructor == terms.DescCons.cons then
		local details = arg:unwrap_tuple_value()
		local tuple_types, n_elements, tuple_vals = make_inner_context(details[1], make_prefix)
		local f = details[2]
		local element_type
		if tuple_types:len() == tuple_vals:len() then
			local prefix = flex_value.tuple_value(tuple_vals)
			element_type = apply_value(f, prefix)
			if element_type:is_singleton() then
				local _, val = element_type:unwrap_singleton()
				tuple_vals:append(val)
			end
		else
			local prefix = make_prefix(n_elements)
			element_type = apply_value(f, prefix)
		end
		tuple_types:append(element_type)
		return tuple_types, n_elements + 1, tuple_vals
	else
		error("infer: unknown tuple type data constructor")
	end
end

---@param subject_type flex_value
---@param subject_value flex_value
---@return flex_value[]
---@return integer
---@return flex_value[]
function infer_tuple_type_unwrapped(subject_type, subject_value)
	local desc, make_prefix = make_tuple_prefix(subject_type, subject_value)
	return make_inner_context(desc, make_prefix)
end

---@param subject_type flex_value
---@param subject_value flex_value
---@return flex_value[]
---@return integer
---@return flex_value[]
function infer_tuple_type(subject_type, subject_value)
	-- define how the type of each tuple element should be evaluated
	return infer_tuple_type_unwrapped(subject_type, subject_value)
end

---@param desc_a flex_value `flex_value.enum_value`
---@param make_prefix_a fun(i: integer): flex_value
---@param l_ctx TypecheckingContext
---@param desc_b flex_value `flex_value.enum_value`
---@param make_prefix_b fun(i: integer): flex_value
---@param r_ctx TypecheckingContext
---@return boolean ok
---@return ArrayType|string tuple_types_a array(flex_value)
---@return ArrayType tuple_types_b array(flex_value)
---@return ArrayType tuple_vals array(flex_value)
---@return integer n_elements
function make_inner_context2(desc_a, make_prefix_a, l_ctx, desc_b, make_prefix_b, r_ctx)
	local constructor_a, arg_a = desc_a:unwrap_enum_value()
	local constructor_b, arg_b = desc_b:unwrap_enum_value()
	if constructor_a == terms.DescCons.empty and constructor_b == terms.DescCons.empty then
		return true, flex_value_array(), flex_value_array(), flex_value_array(), 0
	elseif constructor_a == terms.DescCons.empty or constructor_b == terms.DescCons.empty then
		return false, "length-mismatch"
	elseif constructor_a == terms.DescCons.cons and constructor_b == terms.DescCons.cons then
		local details_a = arg_a:unwrap_tuple_value()
		local details_b = arg_b:unwrap_tuple_value()
		local ok, tuple_types_a, tuple_types_b, tuple_vals, n_elements =
			make_inner_context2(details_a[1], make_prefix_a, l_ctx, details_b[1], make_prefix_b, r_ctx)
		if not ok then
			---@cast tuple_types_a string
			return ok, tuple_types_a
		end
		---@cast tuple_types_a -string
		local f_a = details_a[2] --[[@as flex_value]]
		local f_b = details_b[2] --[[@as flex_value]]
		---@type flex_value
		local element_type_a
		---@type flex_value
		local element_type_b
		if tuple_types_a:len() == tuple_vals:len() then
			local prefix = flex_value.tuple_value(tuple_vals)
			element_type_a = apply_value(f_a, prefix, l_ctx)
			element_type_b = apply_value(f_b, prefix, l_ctx) -- This looks wrong but it's necessary to fix a missing placeholder problem

			if element_type_a:is_singleton() then
				local _, val = element_type_a:unwrap_singleton()
				tuple_vals:append(val)
			elseif element_type_b:is_singleton() then
				error("singleton found in tuple use, this doesn't make sense")
				local _, val = element_type_b:unwrap_singleton()
				tuple_vals:append(val)
			end
		else
			local prefix_a = make_prefix_a(n_elements)
			local prefix_b = make_prefix_b(n_elements)
			element_type_a = apply_value(f_a, prefix_a, l_ctx)
			element_type_b = apply_value(f_b, prefix_b, r_ctx)
		end
		tuple_types_a:append(element_type_a)
		tuple_types_b:append(element_type_b)
		return true, tuple_types_a, tuple_types_b, tuple_vals, n_elements + 1
	else
		return false, "infer: unknown tuple type data constructor"
	end
end

---@param subject_type_a flex_value
---@param l_ctx TypecheckingContext
---@param subject_type_b flex_value
---@param r_ctx TypecheckingContext
---@param subject_value flex_value
---@return boolean ok
---@return flex_value[]|string tuple_types_a
---@return flex_value[] tuple_types_b
---@return flex_value[] tuple_vals
---@return integer n_elements
function infer_tuple_type_unwrapped2(subject_type_a, l_ctx, subject_type_b, r_ctx, subject_value)
	local desc_a, make_prefix_a = make_tuple_prefix(subject_type_a, subject_value)
	local desc_b, make_prefix_b = make_tuple_prefix(subject_type_b, subject_value)
	return make_inner_context2(desc_a, make_prefix_a, l_ctx, desc_b, make_prefix_b, r_ctx)
end

---@overload fun(inferrable_term : inferrable, typechecking_context : TypecheckingContext) : boolean, string
---@param inferrable_term inferrable
---@param typechecking_context TypecheckingContext
---@return boolean ok
---@return flex_value type
---@return ArrayValue usages
---@return typed term
local function infer_impl(
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
		local index, debuginfo = inferrable_term:unwrap_bound_variable()
		local typeof_bound = typechecking_context:get_type(index)
		local usage_counts = usage_array()
		local context_size = typechecking_context:len()
		for _ = 1, context_size do
			usage_counts:append(0)
		end
		usage_counts[index] = 1
		local bound = typed_term.bound_variable(index, debuginfo)
		return true, typeof_bound, usage_counts, bound
	elseif inferrable_term:is_annotated() then
		local checkable_term, inferrable_goal_type = inferrable_term:unwrap_annotated()
		local ok, type_of_type, usages, goal_typed_term = infer(inferrable_goal_type, typechecking_context)
		if not ok then
			return false, type_of_type
		end
		local goal_type = evaluate(goal_typed_term, typechecking_context.runtime_context, typechecking_context)
		local ok, el_usages, el_term = check(checkable_term, typechecking_context, goal_type)
		if not ok then
			---@cast el_usages string
			return false, el_usages
		end
		---@cast el_usages -string
		return true, goal_type, el_usages, el_term
	elseif inferrable_term:is_typed() then
		local type, usage, term = inferrable_term:unwrap_typed()
		return true, evaluate(type, typechecking_context:get_runtime_context(), typechecking_context), usage, term
	elseif inferrable_term:is_annotated_lambda() then
		local param_name, param_annotation, body, start_anchor, param_visibility, purity =
			inferrable_term:unwrap_annotated_lambda()
		local ok, param_type_of_term, _, param_term = infer(param_annotation, typechecking_context)
		if not ok then
			return false, param_type_of_term
		end

		local param_type = evaluate(param_term, typechecking_context:get_runtime_context(), typechecking_context)
		local param_debug = terms.var_debug(param_name, start_anchor)
		local inner_context = typechecking_context:append(param_name, param_type, nil, param_debug)
		local ok, purity_usages, purity_term = check(purity, inner_context, flex_value.strict(terms.host_purity_type))
		if not ok then
			---@cast purity_usages string
			return false, purity_usages
		end
		---@cast purity_usages -string
		local ok, body_type, body_usages, body_term = infer(body, inner_context)
		if not ok then
			return false, body_type
		end

		local elements = typed_array()
		local mappings = {}
		local capture_info = terms.var_debug("#capture", start_anchor)

		for i, v in ipairs(body_usages) do
			if i <= typechecking_context:len() and v > 0 then
				local _, info = typechecking_context:get_runtime_context():get(i)
				elements:append(typed_term.bound_variable(i, info))
				mappings[i] = typed_term.tuple_element_access(typed_term.bound_variable(1, capture_info), #elements)
			end
		end

		local capture = typed_term.tuple_cons(elements)

		local body_value = evaluate(body_term, typechecking_context.runtime_context, typechecking_context)

		local body_term_sub = substitute_inner(body_value, mappings, 2, typechecking_context)

		local result_type = substitute_type_variables(
			body_type,
			param_debug,
			inner_context:len(),
			param_name,
			typechecking_context:get_runtime_context(),
			inner_context
		)
		--[[local result_type = U.tag("substitute_type_variables", {
			body_type = body_type:pretty_preprint(typechecking_context),
			index = inner_context:len(),
			block_level = typechecker_state.block_level,
		}, substitute_type_variables, body_type, inner_context:len(), param_name)]]
		local result_info = flex_value.result_info(
			result_info(
				evaluate(purity_term, typechecking_context:get_runtime_context(), typechecking_context):unwrap_host_value()
			)
		) --TODO make more flexible
		local body_usages_param = body_usages[body_usages:len()]
		local lambda_usages = body_usages:copy(1, body_usages:len() - 1)
		local lambda_type = flex_value.pi(
			param_type,
			flex_value.param_info(flex_value.visibility(param_visibility)),
			result_type,
			result_info
		)
		lambda_type.original_name = param_name
		local lambda_term =
			typed_term.lambda(param_name .. "^", param_debug, body_term_sub, capture, capture_info, start_anchor)
		return true, lambda_type, lambda_usages, lambda_term
	elseif inferrable_term:is_pi() then
		local param_type, param_info, result_type, result_info = inferrable_term:unwrap_pi()
		local ok, param_type_type, param_type_usages, param_type_term = infer(param_type, typechecking_context)
		if not ok then
			return false, param_type_type
		end
		local ok, param_info_usages, param_info_term =
			check(param_info, typechecking_context, flex_value.strict(strict_value.param_info_type))
		if not ok then
			return false, param_info_usages
		end
		local ok, result_type_type, result_type_usages, result_type_term = infer(result_type, typechecking_context)
		if not ok then
			return false, result_type_type
		end
		local ok, result_info_usages, result_info_term =
			check(result_info, typechecking_context, flex_value.strict(strict_value.result_info_type))
		if not ok then
			return false, result_info_usages
		end
		if not result_type_type:is_pi() then
			error "result type of a pi term must infer to a pi because it must be callable"
			-- TODO: switch to using a mechanism term system
		end
		local result_type_param_type, result_type_param_info, result_type_result_type, result_type_result_info =
			result_type_type:unwrap_pi()

		if not result_type_result_info:unwrap_result_info():unwrap_result_info():is_pure() then
			error "result type computation must be pure for now"
		end

		local ok, err = typechecker_state:flow(
			evaluate(param_type_term, typechecking_context.runtime_context, typechecking_context),
			typechecking_context,
			result_type_param_type,
			typechecking_context,
			terms.constraintcause.primitive("inferrable pi term", U.anchor_here())
		)
		if not ok then
			return false, err
		end
		local sort_arg_unique =
			flex_value.stuck(stuck_value.free(free.unique({ debug = "pi infer result type type arg" })))
		local result_type_result_type_result =
			apply_value(result_type_result_type, sort_arg_unique, typechecking_context)
		local sort = flex_value.union_type(
			param_type_type,
			flex_value.union_type(result_type_result_type_result, flex_value.star(0, 0))
		)
		-- local sort = flex_value.star(
		-- 	math.max(nearest_star_level(param_type_type), nearest_star_level(result_type_result_type_result), 0)
		-- )

		local term = typed_term.pi(param_type_term, param_info_term, result_type_term, result_info_term)
		term.original_name = inferrable_term.original_name -- TODO: If this is an inferrable with an anchor, use the anchor information instead

		local usages = usage_array()
		add_arrays(usages, param_type_usages)
		add_arrays(usages, param_info_usages)
		add_arrays(usages, result_type_usages)
		add_arrays(usages, result_info_usages)

		return true, sort, usages, term
	elseif inferrable_term:is_application() then
		local f, arg = inferrable_term:unwrap_application()
		local ok, f_type, f_usages, f_term = infer(f, typechecking_context)
		if not ok then
			return false, f_type
		end

		if f_type:is_pi() then
			local f_param_type, f_param_info, f_result_type, f_result_info = f_type:unwrap_pi()
			local overflow = 0
			while f_param_info:unwrap_param_info():unwrap_visibility():is_implicit() do
				overflow = overflow + 1
				if overflow > 1024 then
					error(
						"Either you have a parameter with more than 1024 implicit parameters or this is an infinite loop!"
					)
				end

				local metavar = typechecker_state:metavariable(typechecking_context)
				local metaresult = apply_value(f_result_type, metavar:as_flex(), typechecking_context)
				if not metaresult:is_pi() then
					error(
						ConstraintError.new(
							"calling function with implicit args, result type applied on implicit args must be a function type: ",
							metaresult,
							typechecking_context
						)
					)
				end
				f_term = typed_term.application(f_term, typed_term.metavariable(metavar))
				f_param_type, f_param_info, f_result_type, f_result_info = metaresult:unwrap_pi()
			end

			local ok, arg_usages, arg_term = check(arg, typechecking_context, f_param_type)
			if not ok then
				return false, arg_usages
			end

			local application_usages = usage_array()
			add_arrays(application_usages, f_usages)
			add_arrays(application_usages, arg_usages)
			local application = typed_term.application(f_term, arg_term)

			-- check already checked for us so no check_concrete
			local arg_value = evaluate(arg_term, typechecking_context:get_runtime_context(), typechecking_context)
			local application_result_type = apply_value(f_result_type, arg_value, typechecking_context)

			if flex_value.value_check(application_result_type) ~= true then
				local bindings = typechecking_context:get_runtime_context().bindings
				error(
					ConstraintError.new(
						"calling function with implicit args, result type applied on implicit args must be a function type: ",
						application_result_type,
						typechecking_context
					)
				)
			end
			return true, application_result_type, application_usages, application
		elseif f_type:is_host_function_type() then
			local f_param_type, f_result_type_closure, f_result_info = f_type:unwrap_host_function_type()

			local ok, arg_usages, arg_term = check(arg, typechecking_context, f_param_type)
			if not ok then
				return false, arg_usages
			end

			local application_usages = usage_array()
			add_arrays(application_usages, f_usages)
			add_arrays(application_usages, arg_usages)
			local application = typed_term.application(f_term, arg_term)

			-- check already checked for us so no check_concrete
			local f_result_type = apply_value(
				f_result_type_closure,
				evaluate(arg_term, typechecking_context:get_runtime_context(), typechecking_context),
				typechecking_context
			)
			if flex_value.value_check(f_result_type) ~= true then
				error("application_result_type isn't a value inferring application of host_function_type")
			end
			return true, f_result_type, application_usages, application
		else
			p(f_type)
			error("infer, is_application, f_type: expected a term with a function type")
		end
	elseif inferrable_term:is_tuple_cons() then
		local elements, info = inferrable_term:unwrap_tuple_cons()
		-- type_data is either "empty", an empty tuple,
		-- or "cons", a tuple with the previous type_data and a function that
		-- takes all previous values and produces the type of the next element
		local type_data = terms.empty
		local usages = usage_array()
		local new_elements = typed_array()
		for i, v in elements:ipairs() do
			local ok, el_type, el_usages, el_term = infer(v, typechecking_context)
			if not ok then
				return false, el_type
			end
			local el_val = evaluate(el_term, typechecking_context.runtime_context, typechecking_context)
			local el_singleton = flex_value.singleton(el_type, el_val)
			type_data = terms.cons(
				type_data,
				substitute_type_variables(
					el_singleton,
					info[i],
					typechecking_context:len() + 1,
					"#tuple-cons-el",
					typechecking_context:get_runtime_context(),
					typechecking_context:append("#tuple-cons-el", flex_value.tuple_type(type_data), nil, info[i])
				)
			)
			add_arrays(usages, el_usages)
			new_elements:append(el_term)
		end
		return true, flex_value.tuple_type(type_data), usages, typed_term.tuple_cons(new_elements)
	elseif inferrable_term:is_host_tuple_cons() then
		error("this code is definitely rot, will not work without rewrites")
		--print "inferring tuple construction"
		--print(inferrable_term:pretty_print())
		--print "environment_names"
		--for i = 1, #typechecking_context do
		--	print(i, typechecking_context:get_name(i))
		--end
		local elements, info = inferrable_term:unwrap_host_tuple_cons()
		-- type_data is either "empty", an empty tuple,
		-- or "cons", a tuple with the previous type_data and a function that
		-- takes all previous values and produces the type of the next element
		-- TODO: it is a type error to put something that isn't a host_value into a host tuple
		local type_data = terms.empty
		local usages = usage_array()
		local new_elements = typed_array()
		for i, v in elements:ipairs() do
			local ok, el_type, el_usages, el_term = infer(v, typechecking_context)
			if not ok then
				return false, el_type
			end
			--print "inferring element of tuple construction"
			--print(el_type:pretty_print())
			local el_val = evaluate(el_term, typechecking_context.runtime_context, typechecking_context)
			local el_singleton = flex_value.singleton(el_type, el_val)
			type_data = terms.cons(
				type_data,
				substitute_type_variables(el_singleton, info[i], typechecking_context:len() + 1),
				"#host-tuple-cons-el",
				typechecking_context:get_runtime_context()
			)
			add_arrays(usages, el_usages)
			new_elements:append(el_term)
		end
		return true, flex_value.host_tuple_type(type_data), usages, typed_term.host_tuple_cons(new_elements)
	elseif inferrable_term:is_tuple_elim() then
		local names, infos, subject, body = inferrable_term:unwrap_tuple_elim()
		local ok, subject_type, subject_usages, subject_term = infer(subject, typechecking_context)
		if not ok then
			return false, subject_type
		end

		-- evaluating the subject is necessary for inferring the type of the body
		local subject_value = evaluate(subject_term, typechecking_context:get_runtime_context(), typechecking_context)

		local desc = terms.empty
		for _ in names:ipairs() do
			local next_elem_type_mv = typechecker_state:metavariable(typechecking_context)
			local next_elem_type = next_elem_type_mv:as_flex()
			desc = terms.cons(desc, next_elem_type)
		end
		local spec_type = flex_value.tuple_type(desc)
		local host_spec_type = flex_value.host_tuple_type(desc)
		local ok, n_elements
		local tupletypes, htupletypes

		ok, tupletypes, n_elements = typechecker_state:speculate(function()
			local ok, err = typechecker_state:flow(
				subject_type,
				typechecking_context,
				spec_type,
				typechecking_context,
				terms.constraintcause.primitive("tuple elimination", U.anchor_here())
			)
			if not ok then
				return false, err
			end
			return true, infer_tuple_type(spec_type, subject_value)
		end)
		--local tupletypes, n_elements = infer_tuple_type(subject_type, subject_value)
		if not ok then
			ok, htupletypes, n_elements = typechecker_state:speculate(function()
				local ok, err = typechecker_state:flow(
					subject_type,
					typechecking_context,
					host_spec_type,
					typechecking_context,
					terms.constraintcause.primitive("host tuple elimination", U.anchor_here())
				)
				if not ok then
					return false, err
				end
				return true, infer_tuple_type(host_spec_type, subject_value)
			end)
			if ok then
				tupletypes = htupletypes
			end
		end

		if not ok then
			--error(tupletypes)
			--error(htupletypes)
			-- try uncommenting one of the error prints above
			-- you need to figure out which one is relevant for your problem
			-- after you're finished, please comment it out so that, next time, the message below can be found again
			error("(infer) tuple elim speculation failed! debugging this is left as an exercise to the maintainer")
		end

		local inner_context = typechecking_context

		for i, v in tupletypes:ipairs() do
			inner_context = inner_context:append(
				names[i] or "#tuple_element_" .. i,
				v,
				index_tuple_value(subject_value, i),
				infos[i]
			)
		end

		-- infer the type of the body, now knowing the type of the tuple
		local ok, body_type, body_usages, body_term = infer(body, inner_context)
		if not ok then
			return false, body_type
		end

		local result_usages = usage_array()
		add_arrays(result_usages, subject_usages)
		add_arrays(result_usages, body_usages)
		return true, body_type, result_usages, typed_term.tuple_elim(names, infos, subject_term, n_elements, body_term)
	elseif inferrable_term:is_tuple_type() then
		local desc = inferrable_term:unwrap_tuple_type()
		local ok, desc_type, desc_usages, desc_term = infer(desc, typechecking_context)
		if not ok then
			return false, desc_type
		end
		local univ_var = typechecker_state:metavariable(typechecking_context, false):as_flex()
		local ok, err = typechecker_state:flow(
			desc_type,
			typechecking_context,
			flex_value.tuple_desc_type(univ_var),
			typechecking_context,
			terms.constraintcause.primitive("tuple type construction", U.anchor_here())
		)
		if not ok then
			return false, err
		end
		return true,
			flex_value.union_type(flex_value.star(0, 0), univ_var),
			desc_usages,
			terms.typed_term.tuple_type(desc_term)
	elseif inferrable_term:is_record_cons() then
		local fields = inferrable_term:unwrap_record_cons()
		-- type_data is either "empty", an empty tuple,
		-- or "cons", a tuple with the previous type_data and a function that
		-- takes all previous values and produces the type of the next element
		local type_data = terms.empty
		local usages = usage_array()
		local new_fields = string_typed_map()
		for k, v in pairs(fields) do
			local ok, field_type, field_usages, field_term = infer(v, typechecking_context)
			if not ok then
				return false, field_type
			end
			type_data = terms.cons(
				type_data,
				strict_value.name(k),
				substitute_type_variables(
					field_type,
					terms.var_debug("#record-cons-el", U.anchor_here()),
					typechecking_context:len() + 1,
					"#record-cons-el",
					typechecking_context:get_runtime_context(),
					typechecking_context
				)
			)
			add_arrays(usages, field_usages)
			new_fields[k] = field_term
		end
		return true, flex_value.record_type(type_data), usages, typed_term.record_cons(new_fields)
	elseif inferrable_term:is_record_elim() then
		local subject, field_names, body = inferrable_term:unwrap_record_elim()
		local ok, subject_type, subject_usages, subject_term = infer(subject, typechecking_context)
		if not ok then
			return false, subject_type
		end
		local ok, desc = subject_type:as_record_type()
		if not ok then
			error("infer, is_record_elim, subject_type: expected a term with a record type")
		end
		-- evaluating the subject is necessary for inferring the type of the body
		local subject_value = evaluate(subject_term, typechecking_context:get_runtime_context(), typechecking_context)

		-- define how the type of each record field should be evaluated
		local make_prefix
		if subject_value:is_record_value() then
			local subject_fields = subject_value:unwrap_record_value()
			function make_prefix(field_names)
				local prefix_fields = string_value_map()
				for _, v in field_names:ipairs() do
					prefix_fields[v] = subject_fields[v]
				end
				return true, flex_value.record_value(prefix_fields)
			end
		elseif subject_value:is_stuck() then
			local subject_stuck_value = subject_value:unwrap_stuck()
			function make_prefix(field_names)
				local prefix_fields = string_value_map()
				for _, v in field_names:ipairs() do
					prefix_fields[v] = flex_value.stuck(stuck_value.record_field_access(subject_stuck_value, v))
				end
				return true, flex_value.record_value(prefix_fields)
			end
		else
			error("infer, is_record_elim, subject_value: expected a record")
		end

		-- evaluate the type of the record
		local function make_type(desc)
			local constructor, arg = desc:unwrap_enum_value()
			if constructor == terms.DescCons.empty then
				return true, string_array(), string_value_map()
			elseif constructor == terms.DescCons.cons then
				local details = arg:unwrap_tuple_value()
				local field_names, field_types = make_type(details[1])
				local name = details[2]:unwrap_name()
				local f = details[3]
				local prefix = make_prefix(field_names)
				local field_type = apply_value(f, prefix, typechecking_context)
				field_names:append(name)
				field_types[name] = field_type
				return true, field_names, field_types
			else
				error("infer: unknown tuple type data constructor")
			end
		end
		local desc_field_names, desc_field_types = make_type(desc)

		-- reorder the fields into the requested order
		local inner_context = typechecking_context
		for _, v in field_names:ipairs() do
			local t = desc_field_types[v]
			if t == nil then
				error("infer: trying to access a nonexistent record field")
			end
			inner_context = inner_context:append(v, t, nil, terms.var_debug(v, U.anchor_here()))
		end

		-- infer the type of the body, now knowing the type of the record
		local ok, body_type, body_usages, body_term = infer(body, inner_context)
		if not ok then
			return false, body_type
		end

		local result_usages = usage_array()
		add_arrays(result_usages, subject_usages)
		add_arrays(result_usages, body_usages)
		return true, body_type, result_usages, typed_term.record_elim(subject_term, field_names, body_term)
	elseif inferrable_term:is_enum_cons() then
		local constructor, arg = inferrable_term:unwrap_enum_cons()
		local ok, arg_type, arg_usages, arg_term = infer(arg, typechecking_context)
		if not ok then
			return false, arg_type
		end
		local variants = string_value_map()
		variants:set(constructor, arg_type)
		local enum_type = flex_value.enum_type(flex_value.enum_desc_value(variants))
		return true, enum_type, arg_usages, typed_term.enum_cons(constructor, arg_term)
	elseif inferrable_term:is_enum_elim() then
		local subject, mechanism = inferrable_term:unwrap_enum_elim()
		local ok, subject_type, subject_usages, subject_term = infer(subject, typechecking_context)
		if not ok then
			return false, subject_type
		end
		-- local ok, desc = subject_type:as_enum_type()
		-- if not ok then
		--   error("infer, is_enum_elim, subject_type: expected a term with an enum type")
		-- end
		local ok, mechanism_type, mechanism_usages, mechanism_term = infer(mechanism, typechecking_context)
		if not ok then
			return false, mechanism_type
		end
		-- TODO: check subject desc against mechanism desc
		error("nyi")
	elseif inferrable_term:is_enum_case() then
		local subject, variants, variant_debug, default = inferrable_term:unwrap_enum_case()
		local ok, subject_type, subject_usages, subject_term = infer(subject, typechecking_context)
		if not ok then
			return false, subject_type
		end
		local constrain_variants = string_value_map()
		for k, v in variants:pairs() do
			constrain_variants:set(k, typechecker_state:metavariable(typechecking_context, false):as_flex())
		end
		local ok, err = typechecker_state:flow(
			subject_type,
			typechecking_context,
			flex_value.enum_type(flex_value.enum_desc_value(constrain_variants)),
			typechecking_context,
			terms.constraintcause.primitive("enum case matching", U.anchor_here())
		)
		if not ok then
			return false, err
		end
		local term_variants = string_typed_map()

		local result_types = {}
		for k, v in variants:pairs() do
			--TODO figure out where to store/retrieve the anchors correctly
			local ok, variant_type, variant_usages, variant_term =
				infer(v, typechecking_context:append("#variant", constrain_variants:get(k), nil, v)) --TODO improve
			if not ok then
				return false, variant_type
			end
			term_variants:set(k, variant_term)
			result_types[#result_types + 1] = variant_type
		end
		local result_type = result_types[1]
		for i = 2, #result_types do
			result_type = flex_value.union_type(result_type, result_types[i])
		end
		local absurd_info = terms.var_debug("#absurd", U.anchor_here())
		return true,
			result_type,
			subject_usages,
			typed_term.enum_case(
				subject_term,
				term_variants,
				variant_debug,
				typed_term.enum_absurd(
					typed_term.bound_variable(typechecking_context:len() + 1, absurd_info),
					"unacceptable enum variant"
				),
				absurd_info
			)
	elseif inferrable_term:is_enum_desc_cons() then
		local variants, rest = inferrable_term:unwrap_enum_desc_cons()
		local result_types = {}
		local term_variants = string_typed_map()
		for k, v in variants:pairs() do
			local ok, variant_type, variant_usages, variant_term = infer(v, typechecking_context) --TODO improve
			if not ok then
				return false, variant_type
			end
			term_variants:set(k, variant_term)
			result_types[#result_types + 1] = variant_type
		end
		local result_type = result_types[1]
		for i = 2, #result_types do
			result_type = flex_value.union_type(result_type, result_types[i])
		end
		local ok, rest_type_of_term, rest_usages, rest_term = infer(rest, typechecking_context) --TODO improve
		if not ok then
			return false, rest_type_of_term
		end
		return true,
			flex_value.enum_desc_type(result_type),
			rest_usages,
			typed_term.enum_desc_cons(term_variants, rest_term)
	elseif inferrable_term:is_enum_type() then
		local desc = inferrable_term:unwrap_enum_type()
		local ok, desc_type, desc_usages, desc_term = infer(desc, typechecking_context)
		if not ok then
			return false, desc_type
		end
		local univ_var = typechecker_state:metavariable(typechecking_context, false):as_flex()
		local ok, err = typechecker_state:flow(
			desc_type,
			typechecking_context,
			flex_value.enum_desc_type(univ_var),
			typechecking_context,
			terms.constraintcause.primitive("enum type construction", U.anchor_here())
		)
		if not ok then
			return false, err
		end
		return true,
			flex_value.union_type(flex_value.star(0, 0), univ_var),
			desc_usages,
			terms.typed_term.enum_type(desc_term)
	elseif inferrable_term:is_object_cons() then
		local methods = inferrable_term:unwrap_object_cons()
		local type_data = terms.empty
		local new_methods = string_typed_map()
		for k, v in pairs(methods) do
			local ok, method_type, method_usages, method_term = infer(v, typechecking_context)
			if not ok then
				return false, method_type
			end

			type_data = terms.cons(type_data, strict_value.name(k), method_type)
			new_methods[k] = method_term
		end
		-- TODO: usages
		return true, flex_value.object_type(type_data), usage_array(), typed_term.object_cons(new_methods)
	elseif inferrable_term:is_object_elim() then
		local subject, mechanism = inferrable_term:unwrap_object_elim()
		error("nyi")
	elseif inferrable_term:is_operative_cons() then
		local operative_type, userdata = inferrable_term:unwrap_operative_cons()
		local ok, operative_type_type, operative_type_usages, operative_type_term =
			infer(operative_type, typechecking_context)
		if not ok then
			return false, operative_type_type
		end
		local operative_type_value =
			evaluate(operative_type_term, typechecking_context:get_runtime_context(), typechecking_context)
		local ok, userdata_type, userdata_usages, userdata_term = infer(userdata, typechecking_context)
		if not ok then
			return false, userdata_type
		end
		local ok, op_handler, op_userdata_type = operative_type_value:as_operative_type()
		if not ok then
			error("infer, is_operative_cons, operative_type_value: expected a term with an operative type")
		end
		if userdata_type ~= op_userdata_type then
			local ok, err = typechecker_state:flow(
				userdata_type,
				typechecking_context,
				op_userdata_type,
				typechecking_context,
				terms.constraintcause.primitive("operative userdata", U.anchor_here())
			)
			if not ok then
				return false, err
			end
		end
		local operative_usages = usage_array()
		add_arrays(operative_usages, operative_type_usages)
		add_arrays(operative_usages, userdata_usages)
		return true, operative_type_value, operative_usages, typed_term.operative_cons(userdata_term)
	elseif inferrable_term:is_operative_type_cons() then
		local handler, userdata_type = inferrable_term:unwrap_operative_type_cons()
		local goal_type = flex_value.pi(
			flex_value.tuple_type(
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
				flex_value.tuple_type(
					terms.tuple_desc(
						const_combinator(host_inferrable_term_type),
						const_combinator(host_environment_type)
					)
				)
			),
			--unrestricted(tup_val(unrestricted(host_inferrable_term_type), unrestricted(host_environment_type))),
			result_info_pure
		)
		local ok, handler_usages, handler_term = check(handler, typechecking_context, goal_type)
		if not ok then
			return false, handler_usages
		end
		local ok, userdata_type_type, userdata_type_usages, userdata_type_term =
			infer(userdata_type, typechecking_context)
		if not ok then
			return false, userdata_type_type
		end
		local operative_type_usages = usage_array()
		add_arrays(operative_type_usages, handler_usages)
		add_arrays(operative_type_usages, userdata_type_usages)
		local handler_level = get_level(goal_type)
		local userdata_type_level = get_level(userdata_type_type)
		local operative_type_level = math.max(handler_level, userdata_type_level)
		return true,
			flex_value.star(operative_type_level, 0),
			operative_type_usages,
			typed_term.operative_type_cons(handler_term, userdata_type_term)
	elseif inferrable_term:is_host_user_defined_type_cons() then
		local id, family_args = inferrable_term:unwrap_host_user_defined_type_cons()
		local new_family_args = typed_array()
		local result_usages = usage_array()
		for _, v in family_args:ipairs() do
			local ok, e_type, e_usages, e_term = infer(v, typechecking_context)
			if not ok then
				return false, e_type
			end
			-- FIXME: use e_type?
			add_arrays(result_usages, e_usages)
			new_family_args:append(e_term)
		end
		return true,
			strict_value.host_type_type,
			result_usages,
			typed_term.host_user_defined_type_cons(id, new_family_args)
	elseif inferrable_term:is_host_wrapped_type() then
		local type_inf = inferrable_term:unwrap_host_wrapped_type()
		local ok, content_type_type, content_type_usages, content_type_term = infer(type_inf, typechecking_context)
		if not ok then
			return false, content_type_type
		end
		if not is_type_of_types(content_type_type) then
			error "infer: type being boxed must be a type"
		end
		return true, strict_value.host_type_type, content_type_usages, typed_term.host_wrapped_type(content_type_term)
	elseif inferrable_term:is_host_wrap() then
		local content = inferrable_term:unwrap_host_wrap()
		local ok, content_type, content_usages, content_term = infer(content, typechecking_context)
		if not ok then
			return false, content_type
		end
		return true, flex_value.host_wrapped_type(content_type), content_usages, typed_term.host_wrap(content_term)
	elseif inferrable_term:is_host_unstrict_wrap() then
		local content = inferrable_term:unwrap_host_wrap()
		local ok, content_type, content_usages, content_term = infer(content, typechecking_context)
		if not ok then
			return false, content_type
		end
		return true,
			flex_value.host_unstrict_wrapped_type(content_type),
			content_usages,
			typed_term.host_unstrict_wrap(content_term)
	elseif inferrable_term:is_host_unwrap() then
		local container = inferrable_term:unwrap_host_unwrap()
		local ok, container_type, container_usages, container_term = infer(container, typechecking_context)
		if not ok then
			return false, container_type
		end
		local content_type = container_type:unwrap_host_wrapped_type()
		return true, content_type, container_usages, typed_term.host_unwrap(container_term)
	elseif inferrable_term:is_host_unstrict_unwrap() then
		local container = inferrable_term:unwrap_host_unwrap()
		local ok, container_type, container_usages, container_term = infer(container, typechecking_context)
		if not ok then
			return false, container_type
		end
		local content_type = container_type:unwrap_host_unstrict_wrapped_type()
		return true, content_type, container_usages, typed_term.host_unstrict_unwrap(container_term)
	elseif inferrable_term:is_host_if() then
		local subject, consequent, alternate = inferrable_term:unwrap_host_if()
		-- for each thing in typechecking context check if it == the subject, replace with literal true
		-- same for alternate but literal false

		-- TODO: Replace this with a metavariable that both branches are put into
		local ok, susages, sterm = check(subject, typechecking_context, flex_value.host_bool_type)
		if not ok then
			return false, susages
		end
		local ok, ctype, cusages, cterm = infer(consequent, typechecking_context)
		if not ok then
			return false, ctype
		end
		local ok, atype, ausages, aterm = infer(alternate, typechecking_context)
		if not ok then
			return false, ctype
		end
		local restype = typechecker_state:metavariable(typechecking_context):as_flex()
		local ok, err = typechecker_state:flow(
			ctype,
			typechecking_context,
			restype,
			typechecking_context,
			terms.constraintcause.primitive("inferred host if consequent", U.anchor_here())
		)
		if not ok then
			return false, err
		end
		local ok, err = typechecker_state:flow(
			atype,
			typechecking_context,
			restype,
			typechecking_context,
			terms.constraintcause.primitive("inferred host if alternate", U.anchor_here())
		)
		if not ok then
			return false, err
		end

		local result_usages = usage_array()
		add_arrays(result_usages, susages)
		-- FIXME: max of cusages and ausages rather than adding?
		add_arrays(result_usages, cusages)
		add_arrays(result_usages, ausages)
		return true, restype, result_usages, typed_term.host_if(sterm, cterm, aterm)
	elseif inferrable_term:is_let() then
		local name, debuginfo, expr, body = inferrable_term:unwrap_let()
		local ok, exprtype, exprusages, exprterm = infer(expr, typechecking_context)
		if not ok then
			return false, exprtype
		end
		typechecking_context = typechecking_context:append(
			name,
			exprtype,
			evaluate(exprterm, typechecking_context.runtime_context, typechecking_context),
			debuginfo
		)
		local ok, bodytype, bodyusages, bodyterm = infer(body, typechecking_context)
		if not ok then
			return false, bodytype
		end

		local result_usages = usage_array()
		-- NYI usages are fucky, should remove ones not used in body
		add_arrays(result_usages, exprusages)
		add_arrays(result_usages, bodyusages)
		return true, bodytype, result_usages, terms.typed_term.let(name, debuginfo, exprterm, bodyterm)
	elseif inferrable_term:is_host_intrinsic() then
		local source, type, start_anchor = inferrable_term:unwrap_host_intrinsic()
		local ok, source_usages, source_term =
			check(source, typechecking_context, flex_value.strict(strict_value.host_string_type))
		if not ok then
			return false, source_usages
		end
		local ok, type_type, type_usages, type_term = infer(type, typechecking_context) --check(type, typechecking_context, flex_value.qtype_type(0))
		if not ok then
			return false, type_type
		end

		--print("host intrinsic is inferring: (inferrable term follows)")
		--print(type:pretty_print(typechecking_context))
		--print("lowers to: (typed term follows)")
		--print(type_term:pretty_print(typechecking_context))
		--error "weird type"
		-- FIXME: type_type, source_type are ignored, need checked?
		local type_val = evaluate(type_term, typechecking_context.runtime_context, typechecking_context)
		return true, type_val, source_usages, typed_term.host_intrinsic(source_term, start_anchor)
	elseif inferrable_term:is_level_max() then
		local level_a, level_b = inferrable_term:unwrap_level_max()
		local ok, arg_type_a, arg_usages_a, arg_term_a = infer(level_a, typechecking_context)
		if not ok then
			return false, arg_type_a
		end
		local ok, arg_type_b, arg_usages_b, arg_term_b = infer(level_b, typechecking_context)
		if not ok then
			return false, arg_type_b
		end
		return true, flex_value.level_type, usage_array(), typed_term.level_max(arg_term_a, arg_term_b)
	elseif inferrable_term:is_level_suc() then
		local previous_level = inferrable_term:unwrap_level_suc()
		local ok, arg_type, arg_usages, arg_term = infer(previous_level, typechecking_context)
		if not ok then
			return false, arg_type
		end
		return true, flex_value.level_type, usage_array(), typed_term.level_suc(arg_term)
	elseif inferrable_term:is_level0() then
		return true, flex_value.level_type, usage_array(), typed_term.level0
	elseif inferrable_term:is_host_function_type() then
		local args, returns, res_info = inferrable_term:unwrap_host_function_type()
		local ok, arg_type, arg_usages, arg_term = infer(args, typechecking_context)
		if not ok then
			return false, arg_type
		end
		local ok, return_type, return_usages, return_term = infer(returns, typechecking_context)
		if not ok then
			return false, return_type
		end
		local ok, resinfo_usages, resinfo_term = check(res_info, typechecking_context, flex_value.result_info_type)
		if not ok then
			return false, resinfo_usages
		end
		local res_usages = usage_array()
		add_arrays(res_usages, arg_usages)
		add_arrays(res_usages, return_usages)
		add_arrays(res_usages, resinfo_usages)
		return true,
			flex_value.host_type_type,
			res_usages,
			typed_term.host_function_type(arg_term, return_term, resinfo_term)
	elseif inferrable_term:is_host_tuple_type() then
		local desc = inferrable_term:unwrap_host_tuple_type()
		local ok, desc_type, desc_usages, desc_term = infer(desc, typechecking_context)
		if not ok then
			return false, desc_type
		end
		local ok, err = typechecker_state:flow(
			desc_type,
			typechecking_context,
			flex_value.tuple_desc_type(flex_value.host_type_type),
			typechecking_context,
			terms.constraintcause.primitive("host tuple type construction", U.anchor_here())
		)
		if not ok then
			return false, err
		end
		return true, flex_value.star(0, 0), desc_usages, terms.typed_term.host_tuple_type(desc_term)
	elseif inferrable_term:is_program_sequence() then
		local first, start_anchor, continue = inferrable_term:unwrap_program_sequence()
		local ok, first_type, first_usages, first_term = infer(first, typechecking_context)
		if not ok then
			return false, first_type
		end

		--local first_effect_sig, first_base_type = first_type:unwrap_program_type()
		local first_effect_sig = typechecker_state:metavariable(typechecking_context):as_flex()
		local first_base_type = typechecker_state:metavariable(typechecking_context):as_flex()
		local ok, err = typechecker_state:flow(
			first_type,
			typechecking_context,
			flex_value.program_type(first_effect_sig, first_base_type),
			typechecking_context,
			terms.constraintcause.primitive("Inferring on program type ", start_anchor)
		)
		if not ok then
			return false, err
		end

		local inner_context = typechecking_context:append(
			"#program-sequence",
			first_base_type,
			nil,
			var_debug("#program-sequence", start_anchor)
		)
		local ok, continue_type, continue_usages, continue_term = infer(continue, inner_context)
		if not ok then
			return false, continue_type
		end
		if not continue_type:is_program_type() then
			error(
				ConstraintError.new(
					"rest of the program sequence must infer to a program type: ",
					continue,
					inner_context,
					"\nbut it infers to ",
					continue_type,
					inner_context
				)
			)
		end

		local continue_effect_sig, continue_base_type = continue_type:unwrap_program_type()
		local first_is_row, first_components, first_rest = first_effect_sig:as_effect_row_extend()
		local continue_is_row, continue_components, continue_rest = continue_effect_sig:as_effect_row_extend()
		local result_effect_sig
		if first_is_row and continue_is_row then
			if not first_rest:is_effect_empty() or not continue_rest:is_effect_empty() then
				error("nyi polymorphic effects")
			end
			result_effect_sig =
				flex_value.effect_row_extend(first_components:union(continue_components), flex_value.effect_empty)
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
				error(
					ConstraintError.new(
						"unknown effect sig",
						first_effect_sig,
						inner_context,
						" vs ",
						continue_effect_sig,
						inner_context
					)
				)
			end
			result_effect_sig = flex_value.effect_empty
		end
		local result_usages = usage_array()
		add_arrays(result_usages, first_usages)
		add_arrays(result_usages, continue_usages)
		return true,
			flex_value.program_type(result_effect_sig, continue_base_type),
			result_usages,
			typed_term.program_sequence(first_term, continue_term)
	elseif inferrable_term:is_program_end() then
		local result = inferrable_term:unwrap_program_end()
		local ok, program_type, program_usages, program_term = infer(result, typechecking_context)
		if not ok then
			return false, program_type
		end
		return true,
			flex_value.program_type(flex_value.effect_empty, program_type),
			program_usages,
			typed_term.program_end(program_term)
	elseif inferrable_term:is_program_type() then
		local effect_type, result_type = inferrable_term:unwrap_program_type()
		local ok, effect_type_type, effect_type_usages, effect_type_term = infer(effect_type, typechecking_context)
		if not ok then
			return false, effect_type_type
		end
		local ok, result_type_type, result_type_usages, result_type_term = infer(result_type, typechecking_context)
		if not ok then
			return false, result_type_type
		end
		local res_usages = usage_array()
		add_arrays(res_usages, effect_type_usages)
		add_arrays(res_usages, result_type_usages)
		-- TODO: use biunification constraints for start level
		return true, flex_value.star(0, 0), res_usages, typed_term.program_type(effect_type_term, result_type_term)
	else
		error("infer: unknown kind: " .. inferrable_term.kind)
	end

	error("unreachable!?")
end

---@overload fun(inferrable_term : inferrable, typechecking_context : TypecheckingContext) : boolean, string
---@param inferrable_term inferrable
---@param typechecking_context TypecheckingContext
---@return boolean ok
---@return flex_value type
---@return ArrayValue usages
---@return typed term
function infer(inferrable_term, typechecking_context)
	local tracked = inferrable_term.track ~= nil
	if tracked then
		print(
			"\n" .. string.rep("·", recurse_count) .. "INFER: " .. inferrable_term:pretty_print(typechecking_context)
		)
		--print(typechecking_context:format_names())
	end

	recurse_count = recurse_count + 1
	local ok, v, usages, term = infer_impl(inferrable_term, typechecking_context)
	if ok and not flex_value.value_check(v) then
		error("infer didn't return a flex_value!")
	end
	recurse_count = recurse_count - 1

	if tracked then
		if not ok then
			print(v)
		end

		print(
			string.rep("·", recurse_count)
				.. " → "
				.. term:pretty_print(typechecking_context)
				.. " : "
				.. v:pretty_print(typechecking_context)
		)
		--print(typechecking_context:format_names())
		--v.track = {}
		term.track = {}
	end
	return ok, v, usages, term
end

local intrinsic_memo = setmetatable({}, { __mode = "v" })

---evaluate a typed term in a contextual
---@param typed_term typed
---@param runtime_context FlexRuntimeContext
---@param ambient_typechecking_context TypecheckingContext
---@return flex_value
local function evaluate_impl(typed_term, runtime_context, ambient_typechecking_context)
	-- -> an alicorn value
	-- TODO: typecheck typed_term and runtime_context?
	if terms.typed_term.value_check(typed_term) ~= true then
		error("evaluate, typed_term: expected a typed term")
	end
	if terms.flex_runtime_context_type.value_check(runtime_context) ~= true then
		error("evaluate, runtime_context: expected a runtime context")
	end

	if typed_term:is_bound_variable() then
		local idx, b_dbg = typed_term:unwrap_bound_variable()
		local rc_val, c_dbg = runtime_context:get(idx)
		if rc_val == nil then
			p(typed_term)
			error("runtime_context:get() for bound_variable returned nil")
		end
		if b_dbg ~= c_dbg then
			error(
				"Debug information doesn't match! Contexts are mismatched! Variable #"
					.. tostring(typed_term["{ID}"])
					.. " thinks it is getting "
					.. tostring(b_dbg)
					.. " but context thinks it has "
					.. tostring(c_dbg)
					.. " at index "
					.. tostring(idx)
			)
		end
		return rc_val
	elseif typed_term:is_literal() then
		return flex_value.strict(typed_term:unwrap_literal())
	elseif typed_term:is_metavariable() then
		return U.notail(flex_value.stuck(stuck_value.free(free.metavariable(typed_term:unwrap_metavariable()))))
	elseif typed_term:is_unique() then
		return U.notail(flex_value.stuck(stuck_value.free(free.unique(typed_term:unwrap_unique()))))
	elseif typed_term:is_lambda() then
		local param_name, param_debug, body, capture, capture_dbg, anchor = typed_term:unwrap_lambda()
		local capture_val = evaluate(capture, runtime_context, ambient_typechecking_context)
		return flex_value.closure(param_name, body, capture_val, capture_dbg, param_debug)
	elseif typed_term:is_pi() then
		local param_type, param_info, result_type, result_info = typed_term:unwrap_pi()
		local param_type_value = evaluate(param_type, runtime_context, ambient_typechecking_context)
		local param_info_value = evaluate(param_info, runtime_context, ambient_typechecking_context)
		local result_type_value = evaluate(result_type, runtime_context, ambient_typechecking_context)
		local result_info_value = evaluate(result_info, runtime_context, ambient_typechecking_context)

		--[[local param_type_value = U.tag(
			"evaluate",
			{ param_type = param_type:pretty_preprint(runtime_context) },
			evaluate,
			param_type,
			runtime_context
		)
		local param_info_value = U.tag(
			"evaluate",
			{ param_info = param_info:pretty_preprint(runtime_context) },
			evaluate,
			param_info,
			runtime_context
		)
		local result_type_value = U.tag(
			"evaluate",
			{ result_type = result_type:pretty_preprint(runtime_context) },
			evaluate,
			result_type,
			runtime_context
		)
		local result_info_value = U.tag(
			"evaluate",
			{ result_info = result_info:pretty_preprint(runtime_context) },
			evaluate,
			result_info,
			runtime_context
		)]]
		local res = flex_value.pi(param_type_value, param_info_value, result_type_value, result_info_value)
		res.original_name = typed_term.original_name
		return res
	elseif typed_term:is_application() then
		local f, arg = typed_term:unwrap_application()

		local f_value = evaluate(f, runtime_context, ambient_typechecking_context)
		--local f_value = U.tag("evaluate", { f = f:pretty_preprint(runtime_context) }, evaluate, f, runtime_context)
		local arg_value = evaluate(arg, runtime_context, ambient_typechecking_context)
		--local arg_value =	U.tag("evaluate", { arg = arg:pretty_preprint(runtime_context) }, evaluate, arg, runtime_context)
		return U.notail(apply_value(f_value, arg_value, ambient_typechecking_context))
		-- if you want to debug things that go through this call, you may comment above and uncomment below
		-- but beware that this single change has caused tremendous performance degradation
		-- on the order of 20x slower
		--return U.notail(
		--	U.tag("apply_value", { f_value = f_value, arg_value = arg_value }, apply_value, f_value, arg_value)
		--)
	elseif typed_term:is_tuple_cons() then
		local elements = typed_term:unwrap_tuple_cons()
		local new_elements = flex_value_array()
		for i, v in elements:ipairs() do
			new_elements:append(evaluate(v, runtime_context, ambient_typechecking_context))
			--new_elements:append(U.tag("evaluate", { ["element_" .. tostring(i)] = v }, evaluate, v, runtime_context))
		end
		return flex_value.tuple_value(new_elements)
	elseif typed_term:is_host_tuple_cons() then
		local elements = typed_term:unwrap_host_tuple_cons()
		local new_elements = host_array()
		local stuck = false
		local stuck_element
		local trailing_values
		for i, v in elements:ipairs() do
			local element_value = evaluate(v, runtime_context, ambient_typechecking_context)
			--local element_value = U.tag("evaluate", { ["element_" .. tostring(i)] = v }, evaluate, v, runtime_context)
			if element_value == nil then
				p("wtf", v.kind)
			end
			---@cast element_value -nil
			if stuck then
				trailing_values:append(element_value)
			elseif element_value:is_host_value() then
				new_elements:append(element_value:unwrap_host_value())
			elseif element_value:is_stuck() then
				stuck = true
				stuck_element = element_value:unwrap_stuck()
				trailing_values = flex_value_array()
			else
				print("term that fails", typed_term)
				print("which element", i)
				print("element_value", element_value)
				error("evaluate, is_host_tuple_cons, element_value: expected a host value")
			end
		end
		if stuck then
			return flex_value.stuck(stuck_value.host_tuple(new_elements, stuck_element, trailing_values))
		else
			return flex_value.host_tuple_value(new_elements)
		end
	elseif typed_term:is_tuple_elim() then
		local names, infos, subject, length, body = typed_term:unwrap_tuple_elim()
		if names:len() ~= length or infos:len() ~= length then
			error("Invalid names or infos length!")
		end
		local subject_value = evaluate(subject, runtime_context, ambient_typechecking_context)
		verify_placeholder_lite(subject_value, ambient_typechecking_context)
		--[[local subject_value = U.tag(
			"evaluate",
			{ subject = subject:pretty_preprint(runtime_context) },
			evaluate,
			subject,
			runtime_context
		)]]
		local inner_context = runtime_context
		if subject_value:is_tuple_value() then
			local subject_elements = subject_value:unwrap_tuple_value()
			if subject_elements:len() ~= length then
				print("tuple has only", subject_elements:len(), "elements but expected", length)
				print("tuple being eliminated", subject_value)
				error("evaluate: mismatch in tuple length from typechecking and evaluation")
			end
			for i = 1, length do
				inner_context = inner_context:append(subject_elements[i], names[i], infos[i])
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
				inner_context = inner_context:append(flex_value.host_value(subject_elements[i]), names[i], infos[i])
			end
			for i = real_length + 1, length do
				inner_context = inner_context:append(flex_value.host_value(nil), names[i], infos[i])
			end
		elseif subject_value:is_stuck() then
			for i = 1, length do
				inner_context = inner_context:append(index_tuple_value(subject_value, i), names[i], infos[i])
			end
		else
			p(subject_value)
			error("evaluate, is_tuple_elim, subject_value: expected a tuple")
		end
		return evaluate(body, inner_context, ambient_typechecking_context)
		--return U.tag("evaluate", { body = body:pretty_preprint(runtime_context) }, evaluate, body, inner_context)
	elseif typed_term:is_tuple_element_access() then
		local tuple_term, index = typed_term:unwrap_tuple_element_access()
		local tuple = evaluate(tuple_term, runtime_context, ambient_typechecking_context)
		--[[local tuple = U.tag(
			"evaluate",
			{ tuple_term = tuple_term:pretty_preprint(runtime_context) },
			evaluate,
			tuple_term,
			runtime_context
		)]]
		return index_tuple_value(tuple, index)
	elseif typed_term:is_tuple_type() then
		local desc_term = typed_term:unwrap_tuple_type()
		local desc = evaluate(desc_term, runtime_context, ambient_typechecking_context)
		--[[local desc = U.tag(
			"evaluate",
			{ desc_term = desc_term:pretty_preprint(runtime_context) },
			evaluate,
			desc_term,
			runtime_context
		)]]
		return flex_value.tuple_type(desc)
	elseif typed_term:is_tuple_desc_type() then
		local universe_term = typed_term:unwrap_tuple_desc_type()
		local universe = evaluate(universe_term, runtime_context, ambient_typechecking_context)
		return flex_value.tuple_desc_type(universe)
	elseif typed_term:is_record_cons() then
		local fields = typed_term:unwrap_record_cons()
		local new_fields = string_value_map()
		for k, v in pairs(fields) do
			new_fields[k] = evaluate(v, runtime_context, ambient_typechecking_context)
			--new_fields[k] = U.tag("evaluate", { ["record_field_" .. tostring(k)] = v }, evaluate, v, runtime_context)
		end
		return flex_value.record_value(new_fields)
	elseif typed_term:is_record_elim() then
		local subject, field_names, body = typed_term:unwrap_record_elim()
		local subject_value = evaluate(subject, runtime_context, ambient_typechecking_context)
		--[[local subject_value = U.tag(
			"evaluate",
			{ subject = subject:pretty_preprint(runtime_context) },
			evaluate,
			subject,
			runtime_context
		)]]
		local inner_context = runtime_context
		if subject_value:is_record_value() then
			local subject_fields = subject_value:unwrap_record_value()
			for _, v in field_names:ipairs() do
				inner_context = inner_context:append(subject_fields[v], v, var_debug(v, U.anchor_here()))
			end
		elseif subject_value:is_stuck() then
			local subject_stuck_value = subject_value:unwrap_stuck()
			for _, v in field_names:ipairs() do
				inner_context = inner_context:append(
					flex_value.stuck(stuck_value.record_field_access(subject_stuck_value, v)),
					v,
					var_debug(v, U.anchor_here())
				)
			end
		else
			error("evaluate, is_record_elim, subject_value: expected a record")
		end
		return evaluate(body, inner_context, ambient_typechecking_context)
		--return U.tag("evaluate", { body = body:pretty_preprint(runtime_context) }, evaluate, body, inner_context)
	elseif typed_term:is_enum_cons() then
		local constructor, arg = typed_term:unwrap_enum_cons()
		local arg_value = evaluate(arg, runtime_context, ambient_typechecking_context)
		--local arg_value = U.tag("evaluate", { arg = arg:pretty_preprint(runtime_context) }, evaluate, arg, runtime_context)
		return flex_value.enum_value(constructor, arg_value)
	elseif typed_term:is_enum_elim() then
		local subject, mechanism = typed_term:unwrap_enum_elim()
		local subject_value = evaluate(subject, runtime_context, ambient_typechecking_context)
		local mechanism_value = evaluate(mechanism, runtime_context, ambient_typechecking_context)
		--[[local subject_value = U.tag(
			"evaluate",
			{ subject = subject:pretty_preprint(runtime_context) },
			evaluate,
			subject,
			runtime_context
		)
		local mechanism_value = U.tag(
			"evaluate",
			{ mechanism = mechanism:pretty_preprint(runtime_context) },
			evaluate,
			mechanism,
			runtime_context
		)]]
		if subject_value:is_enum_value() then
			if mechanism_value:is_object_value() then
				local constructor, arg = subject_value:unwrap_enum_value()
				local methods, capture = mechanism_value:unwrap_object_value()
				local this_method = flex_value.closure(
					"#ENUM_PARAM",
					methods[constructor],
					capture,
					terms.var_debug("", U.anchor_here())
				)
				return apply_value(this_method, arg, ambient_typechecking_context)
			elseif mechanism_value:is_stuck() then
				-- objects and enums are categorical duals
				local mechanism_neutral = mechanism_value:unwrap_stuck()
				return flex_value.stuck(stuck_value.object_elim(subject_value, mechanism_neutral))
			else
				error("evaluate, is_enum_elim, is_enum_value, mechanism_value: expected an object")
			end
		elseif subject_value:is_stuck() then
			local subject_stuck_value = subject_value:unwrap_stuck()
			return flex_value.stuck(stuck_value.enum_elim(mechanism_value, subject_stuck_value))
		else
			error("evaluate, is_enum_elim, subject_value: expected an enum")
		end
	elseif typed_term:is_enum_desc_cons() then
		local variants, rest = typed_term:unwrap_enum_desc_cons()
		local result = string_value_map()
		for k, v in variants:pairs() do
			local v_res = evaluate(v, runtime_context, ambient_typechecking_context)
			result:set(k, v_res)
		end
		local res_rest = evaluate(rest, runtime_context, ambient_typechecking_context)
		if res_rest:is_enum_desc_value() then
			local variants_rest = res_rest:unwrap_enum_desc_value()
			return flex_value.enum_desc_value(result:union(variants_rest, function(a, b)
				return a
			end))
		else
			error "non-concrete enum desc in rest slot, TODO"
		end
	elseif typed_term:is_enum_type() then
		local desc = typed_term:unwrap_enum_type()
		local desc_val = evaluate(desc, runtime_context, ambient_typechecking_context)
		return flex_value.enum_type(desc_val)
	elseif typed_term:is_enum_desc_type() then
		local universe_term = typed_term:unwrap_enum_desc_type()
		local universe = evaluate(universe_term, runtime_context, ambient_typechecking_context)
		return flex_value.enum_desc_type(universe)
	elseif typed_term:is_enum_case() then
		local target, variants, variant_debug, default, default_debug = typed_term:unwrap_enum_case()
		local target_val = evaluate(target, runtime_context, ambient_typechecking_context)
		if target_val:is_enum_value() then
			local variant, arg = target_val:unwrap_enum_value()
			if variants:get(variant) then
				return evaluate(
					variants:get(variant),
					runtime_context:append(arg, variant, variant_debug:get(variant)),
					ambient_typechecking_context
				)
			else
				return evaluate(
					default,
					runtime_context:append(target_val, "default", default_debug),
					ambient_typechecking_context
				)
			end
		else
			error "enum case expression didn't evaluate to an enum_value"
		end
	elseif typed_term:is_enum_absurd() then
		local target, debuginfo = typed_term:unwrap_enum_absurd()
		error("ENUM ABSURD OCCURRED: " .. debuginfo)
	elseif typed_term:is_variance_cons() then
		local positive, srel = typed_term:unwrap_variance_cons()
		local positive_value = evaluate(positive, runtime_context, ambient_typechecking_context)
		--[[local positive_value = U.tag(
			"evaluate",
			{ positive = positive:pretty_preprint(runtime_context) },
			evaluate,
			positive,
			runtime_context
		)]]
		local srel_value = evaluate(srel, runtime_context, ambient_typechecking_context)
		-- local srel_value = U.tag("evaluate", { srel = srel:pretty_preprint(runtime_context) }, evaluate, srel, runtime_context)
		---@type Variance
		local variance = {
			positive = positive_value:unwrap_host_value(),
			srel = srel_value:unwrap_host_value(),
		}
		return flex_value.host_value(variance)
	elseif typed_term:is_variance_type() then
		return flex_value.variance_type(
			evaluate(typed_term:unwrap_variance_type(), runtime_context, ambient_typechecking_context)
		)
	elseif typed_term:is_object_cons() then
		return flex_value.object_value(typed_term:unwrap_object_cons(), runtime_context)
	elseif typed_term:is_object_elim() then
		local subject, mechanism = typed_term:unwrap_object_elim()
		local subject_value = evaluate(subject, runtime_context, ambient_typechecking_context)
		local mechanism_value = evaluate(mechanism, runtime_context, ambient_typechecking_context)
		if subject_value:is_object_value() then
			if mechanism_value:is_enum_value() then
				local methods, capture = subject_value:unwrap_object_value()
				local constructor, arg = mechanism_value:unwrap_enum_value()
				local this_method = flex_value.closure(
					"#OBJECT_PARAM",
					methods[constructor],
					capture,
					terms.var_debug("", U.anchor_here())
				)
				return apply_value(this_method, arg, ambient_typechecking_context)
			elseif mechanism_value:is_stuck() then
				-- objects and enums are categorical duals
				local mechanism_neutral = mechanism_value:unwrap_stuck()
				return flex_value.stuck(stuck_value.enum_elim(subject_value, mechanism_neutral))
			else
				error("evaluate, is_object_elim, is_object_value, mechanism_value: expected an enum")
			end
		elseif subject_value:is_stuck() then
			local subject_stuck_value = subject_value:unwrap_stuck()
			return flex_value.stuck(stuck_value.object_elim(mechanism_value, subject_stuck_value))
		else
			error("evaluate, is_object_elim, subject_value: expected an object")
		end
	elseif typed_term:is_operative_cons() then
		local userdata = typed_term:unwrap_operative_cons()
		local userdata_value = evaluate(userdata, runtime_context, ambient_typechecking_context)
		return flex_value.operative_value(userdata_value)
	elseif typed_term:is_operative_type_cons() then
		local handler, userdata_type = typed_term:unwrap_operative_type_cons()
		local handler_value = evaluate(handler, runtime_context, ambient_typechecking_context)
		local userdata_type_value = evaluate(userdata_type, runtime_context, ambient_typechecking_context)
		return flex_value.operative_type(handler_value, userdata_type_value)
	elseif typed_term:is_host_user_defined_type_cons() then
		local id, family_args = typed_term:unwrap_host_user_defined_type_cons()
		local new_family_args = flex_value_array()
		for _, v in family_args:ipairs() do
			new_family_args:append(evaluate(v, runtime_context, ambient_typechecking_context))
		end
		return flex_value.host_user_defined_type(id, new_family_args)
	elseif typed_term:is_host_wrapped_type() then
		local type_term = typed_term:unwrap_host_wrapped_type()
		local type_value = evaluate(type_term, runtime_context, ambient_typechecking_context)
		return flex_value.host_wrapped_type(type_value)
	elseif typed_term:is_host_unstrict_wrapped_type() then
		local type_term = typed_term:unwrap_host_unstrict_wrapped_type()
		local type_value = evaluate(type_term, runtime_context, ambient_typechecking_context)
		return flex_value.host_wrapped_type(type_value)
	elseif typed_term:is_host_wrap() then
		local content = typed_term:unwrap_host_wrap()
		local content_val = evaluate(content, runtime_context, ambient_typechecking_context)
		if content_val:is_stuck() then
			local nval = content_val:unwrap_stuck()
			if nval:is_host_unwrap() then
				local inner_subj = nval:unwrap_host_unwrap()
				return flex_value.stuck(inner_subj)
			end
			return flex_value.stuck(stuck_value.host_wrap(nval))
		end
		return flex_value.host_value(content_val)
	elseif typed_term:is_host_unstrict_wrap() then
		local content = typed_term:unwrap_host_unstrict_wrap()
		local content_val = evaluate(content, runtime_context, ambient_typechecking_context)
		return flex_value.host_value(content_val)
	elseif typed_term:is_host_unwrap() then
		local unwrapped = typed_term:unwrap_host_unwrap()
		local unwrap_val = evaluate(unwrapped, runtime_context, ambient_typechecking_context)
		if not unwrap_val.as_host_value then
			print("unwrapped", unwrapped, unwrap_val)
			error "evaluate, is_host_unwrap: missing as_host_value on unwrapped host_unwrap"
		end

		verify_placeholder_lite(unwrap_val, ambient_typechecking_context)
		if unwrap_val:is_host_value() then
			return flex_value.strict(unwrap_val:unwrap_host_value())
		elseif unwrap_val:is_stuck() then
			local nval = unwrap_val:unwrap_stuck()
			if nval:is_host_wrap() then
				return flex_value.stuck(nval:unwrap_host_wrap())
			else
				return flex_value.stuck(stuck_value.host_unwrap(nval))
			end
		else
			print("unrecognized value in unbox", unwrap_val)
			error "invalid value in unbox, must be host_value or neutral"
		end
	elseif typed_term:is_host_unstrict_unwrap() then
		local unwrapped = typed_term:unwrap_host_unstrict_unwrap()
		local unwrap_val = evaluate(unwrapped, runtime_context, ambient_typechecking_context)
		if not unwrap_val.as_host_value then
			print("unwrapped", unwrapped, unwrap_val)
			error "evaluate, is_host_unwrap: missing as_host_value on unwrapped host_unwrap"
		end
		if unwrap_val:is_host_value() then
			return unwrap_val:unwrap_host_value()
		elseif unwrap_val:is_stuck() then
			local nval = unwrap_val:unwrap_stuck()
			return flex_value.stuck(stuck_value.host_unwrap(nval))
		else
			print("unrecognized value in unbox", unwrap_val)
			error "invalid value in unbox, must be host_value or neutral"
		end
	elseif typed_term:is_host_if() then
		local subject, consequent, alternate = typed_term:unwrap_host_if()
		local sval = evaluate(subject, runtime_context, ambient_typechecking_context)
		if sval:is_host_value() then
			local sbool = sval:unwrap_host_value()
			if type(sbool) ~= "boolean" then
				error("subject of host_if must be a host bool")
			end
			if sbool then
				return evaluate(consequent, runtime_context, ambient_typechecking_context)
			else
				return evaluate(alternate, runtime_context, ambient_typechecking_context)
			end
		elseif sval:is_stuck() then
			local sval_neutral = sval:unwrap_stuck()
			local inner_context_c, inner_context_a = runtime_context, runtime_context
			local ok, index = subject:as_bound_variable()
			if ok then
				inner_context_c = inner_context_c:set(index, flex_value.host_value(true))
				inner_context_a = inner_context_a:set(index, flex_value.host_value(false))
			end
			local cval = evaluate(consequent, inner_context_c, ambient_typechecking_context)
			local aval = evaluate(alternate, inner_context_a, ambient_typechecking_context)
			return flex_value.stuck(stuck_value.host_if(sval_neutral, cval, aval))
		else
			error("subject of host_if must be host_value or neutral")
		end
	elseif typed_term:is_let() then
		local name, let_debug, expr, body = typed_term:unwrap_let()
		local expr_value = evaluate(expr, runtime_context, ambient_typechecking_context)
		return evaluate(body, runtime_context:append(expr_value, name, let_debug), ambient_typechecking_context)
	elseif typed_term:is_host_intrinsic() then
		local source, start_anchor = typed_term:unwrap_host_intrinsic()
		local source_val = evaluate(source, runtime_context, ambient_typechecking_context)
		if source_val:is_host_value() then
			local source_str = source_val:unwrap_host_value()
			if intrinsic_memo[source_str] then
				return flex_value.host_value(intrinsic_memo[source_str])
			end
			local load_env = {}
			for k, v in pairs(_G) do
				load_env[k] = v
			end
			for k, v in pairs(internals_interface) do
				load_env[k] = v
			end
			local has_luvit_require, require_generator = pcall(require, "require")
			if has_luvit_require then
				load_env.require = require_generator(start_anchor.sourceid)
			end
			local res = assert(load(source_str, "host_intrinsic<" .. tostring(start_anchor) .. ">", "t", load_env))()
			intrinsic_memo[source_str] = res
			return flex_value.host_value(res)
		elseif source_val:is_stuck() then
			local source_neutral = source_val:unwrap_stuck()
			return flex_value.stuck(stuck_value.host_intrinsic(source_neutral, start_anchor))
		else
			error "Tried to load an intrinsic with something that isn't a string"
		end
	elseif typed_term:is_host_function_type() then
		local args, returns, res_info = typed_term:unwrap_host_function_type()
		local args_val = evaluate(args, runtime_context, ambient_typechecking_context)
		local returns_val = evaluate(returns, runtime_context, ambient_typechecking_context)
		local resinfo_val = evaluate(res_info, runtime_context, ambient_typechecking_context)
		return flex_value.host_function_type(args_val, returns_val, resinfo_val)
	elseif typed_term:is_level0() then
		return flex_value.level(0)
	elseif typed_term:is_level_suc() then
		local previous_level = typed_term:unwrap_level_suc()
		local previous_level_value = evaluate(previous_level, runtime_context, ambient_typechecking_context)
		local ok, level = previous_level_value:as_level()
		if not ok then
			p(previous_level_value)
			error "wrong type for previous_level"
		end
		if level > OMEGA then
			error("NYI: level too high for typed_level_suc" .. tostring(level))
		end
		return flex_value.level(level + 1)
	elseif typed_term:is_level_max() then
		local level_a, level_b = typed_term:unwrap_level_max()
		local level_a_value = evaluate(level_a, runtime_context, ambient_typechecking_context)
		local level_b_value = evaluate(level_b, runtime_context, ambient_typechecking_context)
		local oka, level_a_level = level_a_value:as_level()
		local okb, level_b_level = level_b_value:as_level()
		if not oka or not okb then
			error "wrong type for level_a or level_b"
		end
		return flex_value.level(math.max(level_a_level, level_b_level))
	elseif typed_term:is_level_type() then
		return flex_value.level_type
	elseif typed_term:is_star() then
		local level, depth = typed_term:unwrap_star()
		return flex_value.star(level, depth)
	elseif typed_term:is_prop() then
		local level = typed_term:unwrap_prop()
		return flex_value.prop(level)
	elseif typed_term:is_host_tuple_type() then
		local desc = typed_term:unwrap_host_tuple_type()
		local desc_val = evaluate(desc, runtime_context, ambient_typechecking_context)
		return flex_value.host_tuple_type(desc_val)
	elseif typed_term:is_range() then
		local lower_bounds, upper_bounds, relation = typed_term:unwrap_range()
		local lower_acc, upper_acc = flex_value_array(), flex_value_array()

		for _, v in lower_bounds:ipairs() do
			lower_acc:append(evaluate(v, runtime_context, ambient_typechecking_context))
		end

		for _, v in upper_bounds:ipairs() do
			upper_acc:append(evaluate(v, runtime_context, ambient_typechecking_context))
		end

		local reln = evaluate(relation, runtime_context, ambient_typechecking_context)

		return flex_value.range(lower_acc, upper_acc, reln)
	elseif typed_term:is_singleton() then
		local supertype, val = typed_term:unwrap_singleton()
		local supertype_val = evaluate(supertype, runtime_context, ambient_typechecking_context)
		local val_val = evaluate(val, runtime_context, ambient_typechecking_context)
		return flex_value.singleton(supertype_val, val_val)
	elseif typed_term:is_program_sequence() then
		local first, rest = typed_term:unwrap_program_sequence()
		local startprog = evaluate(first, runtime_context, ambient_typechecking_context)
		if startprog:is_program_end() then
			local first_res = startprog:unwrap_program_end()
			return evaluate(
				rest,
				runtime_context:append(first_res, "program_end", var_debug("", U.anchor_here())),
				ambient_typechecking_context
			)
		elseif startprog:is_program_cont() then
			local effect_id, effect_arg, cont = startprog:unwrap_program_cont()
			local restframe = terms.continuation.frame(runtime_context, rest)
			return flex_value.program_cont(effect_id, effect_arg, terms.continuation.sequence(cont, restframe))
		else
			error(
				ConstraintError.new(
					"unrecognized program variant: expected program_end or program_cont, got ",
					startprog,
					ambient_typechecking_context
				)
			)
		end
	elseif typed_term:is_program_end() then
		local result = typed_term:unwrap_program_end()

		return flex_value.program_end(evaluate(result, runtime_context, ambient_typechecking_context))
	elseif typed_term:is_program_invoke() then
		local effect_term, arg_term = typed_term:unwrap_program_invoke()
		local effect_val = evaluate(effect_term, runtime_context, ambient_typechecking_context)
		local arg_val = evaluate(arg_term, runtime_context, ambient_typechecking_context)
		if effect_val:is_effect_elem() then
			local effect_id = effect_val:unwrap_effect_elem()
			return flex_value.program_cont(effect_id, arg_val, terms.continuation.empty)
		end
		error "NYI stuck program invoke"
	elseif typed_term:is_program_type() then
		local effect_type, result_type = typed_term:unwrap_program_type()
		local effect_type_val = evaluate(effect_type, runtime_context, ambient_typechecking_context)
		local result_type_val = evaluate(result_type, runtime_context, ambient_typechecking_context)
		return flex_value.program_type(effect_type_val, result_type_val)
	elseif typed_term:is_srel_type() then
		local target = typed_term:unwrap_srel_type()
		return flex_value.srel_type(evaluate(target, runtime_context, ambient_typechecking_context))
	elseif typed_term:is_constrained_type() then
		local mv_ctx = ambient_typechecking_context
		local ctx = ambient_typechecking_context
		local constraints, ignored_mv_ctx = typed_term:unwrap_constrained_type()
		local mv = typechecker_state:metavariable(mv_ctx, false)
		for i, constraint in constraints:ipairs() do
			---@cast constraint constraintelem
			if constraint:is_sliced_constrain() then
				local rel, right, ignored_ctx, cause = constraint:unwrap_sliced_constrain()
				local ok, err = typechecker_state:send_constrain(
					mv_ctx,
					mv:as_flex(),
					rel,
					ctx,
					evaluate(right, runtime_context, ambient_typechecking_context),
					cause
				)
				if not ok then
					error(err)
				end
			elseif constraint:is_constrain_sliced() then
				local left, ignored_ctx, rel, cause = constraint:unwrap_constrain_sliced()
				local ok, err = typechecker_state:send_constrain(
					ctx,
					evaluate(left, runtime_context, ambient_typechecking_context),
					rel,
					mv_ctx,
					mv:as_flex(),
					cause
				)
				if not ok then
					error(err)
				end
			elseif constraint:is_sliced_leftcall() then
				local arg, rel, right, ignored_ctx, cause = constraint:unwrap_sliced_leftcall()
				local ok, err = typechecker_state:send_constrain(
					mv_ctx,
					apply_value(
						mv:as_flex(),
						evaluate(arg, runtime_context, ambient_typechecking_context),
						ambient_typechecking_context
					),
					rel,
					ctx,
					evaluate(right, runtime_context, ambient_typechecking_context),
					cause
				)
				if not ok then
					error(err)
				end
			elseif constraint:is_leftcall_sliced() then
				local left, ignored_ctx, arg, rel, cause = constraint:unwrap_leftcall_sliced()
				local ok, err = typechecker_state:send_constrain(
					ctx,
					apply_value(
						evaluate(left, runtime_context, ambient_typechecking_context),
						evaluate(arg, runtime_context, ambient_typechecking_context),
						ambient_typechecking_context
					),
					rel,
					mv_ctx,
					mv:as_flex(),
					cause
				)
				if not ok then
					error(err)
				end
			elseif constraint:is_sliced_rightcall() then
				local rel, right, ignored_ctx, arg, cause = constraint:unwrap_sliced_rightcall()
				local ok, err = typechecker_state:send_constrain(
					mv_ctx,
					mv:as_flex(),
					rel,
					ctx,
					apply_value(
						evaluate(right, runtime_context, ambient_typechecking_context),
						evaluate(arg, runtime_context, ambient_typechecking_context),
						ambient_typechecking_context
					),
					cause
				)
				if not ok then
					error(err)
				end
			elseif constraint:is_rightcall_sliced() then
				local left, ignored_ctx, rel, arg, cause = constraint:unwrap_rightcall_sliced()
				local ok, err = typechecker_state:send_constrain(
					ctx,
					evaluate(left, runtime_context, ambient_typechecking_context),
					rel,
					mv_ctx,
					apply_value(
						mv:as_flex(),
						evaluate(arg, runtime_context, ambient_typechecking_context),
						ambient_typechecking_context
					),
					cause
				)
				if not ok then
					error(err)
				end
			else
				error "unrecognized constraint kind"
			end
		end
		return mv:as_flex()
	elseif typed_term:is_union_type() then
		local a, b = typed_term:unwrap_union_type()
		return flex_value.union_type(
			evaluate(a, runtime_context, ambient_typechecking_context),
			evaluate(b, runtime_context, ambient_typechecking_context)
		)
	elseif typed_term:is_intersection_type() then
		local a, b = typed_term:unwrap_intersection_type()
		return flex_value.intersection_type(
			evaluate(a, runtime_context, ambient_typechecking_context),
			evaluate(b, runtime_context, ambient_typechecking_context)
		)
	elseif typed_term:is_effect_row_resolve() then
		local ids, rest = typed_term:unwrap_effect_row_resolve()
		return flex_value.effect_row_extend(ids, evaluate(rest, runtime_context, ambient_typechecking_context))
	else
		error("evaluate: unknown kind: " .. typed_term.kind)
	end

	error("unreachable!?")
end

local recurse_count = 0

---evaluate a typed term in a contextual
---@param typed_term typed
---@param runtime_context FlexRuntimeContext
---@param ambient_typechecking_context TypecheckingContext
---@return flex_value
function evaluate(typed_term, runtime_context, ambient_typechecking_context)
	local tracked = typed_term.track ~= nil
	if tracked then
		local input = typed_term:pretty_print(runtime_context)
		print(string.rep("·", recurse_count) .. "EVAL: " .. input)
		--print(runtime_context:format_names())
	end

	verify_placeholder_lite(typed_term, ambient_typechecking_context)
	recurse_count = recurse_count + 1
	local r = evaluate_impl(typed_term, runtime_context, ambient_typechecking_context)
	if not flex_value.value_check(r) then
		error("evaluate didn't return a flex_value after processing: " .. tostring(typed_term))
	end
	recurse_count = recurse_count - 1
	verify_placeholder_lite(r, ambient_typechecking_context)

	if tracked then
		print(string.rep("·", recurse_count) .. " → " .. r:pretty_print(runtime_context))
		--print(runtime_context:format_names())
		r.track = {}
	end
	return r
end

-- evaluate = evaluate_impl

---@alias effect_handler fun(arg: flex_value, cont: flex_continuation): flex_value
---@type {[thread] : {[table] : effect_handler } }
local thread_effect_handlers = setmetatable({}, { __mode = "k" })

---given an evaluated program value, execute it for effects
---@param prog flex_value
---@return flex_value
local function execute_program(prog)
	if prog:is_program_end() then
		return prog:unwrap_program_end()
	elseif prog:is_program_cont() then
		local effect_id, effect_arg, cont = prog:unwrap_program_cont()
		local thr = coroutine.running()
		local handler = thread_effect_handlers[thr][effect_id]
		return handler(effect_arg, cont)
	end
	error "unrecognized program variant"
end

---resume a program after an effect completes
---@param cont flex_continuation
---@param arg flex_value
---@return flex_value
local function invoke_continuation(cont, arg)
	if cont:is_empty() then
		return arg
	elseif cont:is_frame() then
		local ctx, term = cont:unwrap_frame()
		local frame_res = evaluate(term, ctx:append(arg))
		return execute_program(frame_res)
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
	local elements = arg:unwrap_tuple_value()
	---@type flex_value, flex_value
	local func, f_arg = elements:unpack()
	if not func:is_host_value() or not f_arg:is_host_tuple_value() then
		error "host effect information is the wrong kind"
	end
	local res =
		flex_value.host_tuple_value(host_array(func:unwrap_host_value()(f_arg:unwrap_host_tuple_value():unpack())))
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
	constrain = luatovalue(function(l_ctx, val, r_ctx, use, cause)
		return check_concrete(l_ctx, val, r_ctx, use, cause)
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
			U.check_locked(self)
			local args = { ... }
			if #args ~= #v then
				error("Must have one argument per key extractor")
			end

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

	function res:add(obj)
		U.check_locked(self)
		U.append(self._collection, obj)
		local id = #self._collection
		for name, extractors in pairs(indices) do
			self._index_store[name] = U.insert_tree_node(
				obj,
				self._index_store[name],
				1,
				extractors,
				U.getshadowdepth(self._index_store[name])
			)
		end
		return id
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
		for name, extractors in pairs(indices) do
			n._index_store[name] = U.shadowtable(self._index_store[name])
		end
		U.lock_table(self) --  This has to be down here or we'll accidentally copy it

		setmetatable(n, { __shadow = self, __depth = U.getshadowdepth(self) + 1 })
		return n
	end

	function res:commit()
		U.commit(self._collection)
		for name, extractors in pairs(indices) do
			self._index_store[name] = U.commit_tree_node(self._index_store[name], U.getshadowdepth(self))
		end

		local orig = getmetatable(self).__shadow
		U.unlock_table(orig)
		setmetatable(self, nil)
		U.invalidate(self)
	end

	function res:revert()
		U.revert(self._collection)

		for name, extractors in pairs(indices) do
			self._index_store[name] = U.revert_tree_node(self._index_store[name], U.getshadowdepth(self))
			-- It's legal for our top-level node to be below our actual shadow level due to skipped shadows, so we restore those shadow layers here
			-- A commit would have fixed this, but a commit doesn't always happen.
			while U.getshadowdepth(self._index_store[name]) < U.getshadowdepth(self) do
				self._index_store[name] = U.shadowtable(self._index_store[name])
			end
		end

		local orig = getmetatable(self).__shadow
		U.unlock_table(orig)
		setmetatable(self, nil)
		U.invalidate(self)
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
	U.invalidate(self)
end

function TraitRegistry:revert()
	U.revert(self.traits)
	U.invalidate(self)
end

trait_registry_mt = { __index = TraitRegistry }

local function trait_registry()
	return setmetatable({ traits = {} }, trait_registry_mt)
end
---@class TypeCheckerState
---@field pending ReachabilityQueue
---@field graph Reachability
---@field values [flex_value, TypeCheckerTag, TypecheckingContext][]
---@field block_level integer
---@field valcheck { [flex_value]: integer }
---@field usecheck { [flex_value]: integer }
---@field trait_registry TraitRegistry
local TypeCheckerState = {}
--@field values { val: value, tag: TypeCheckerTag, context: TypecheckingContext }

---@alias NodeID integer the ID of a node in the graph

---@class ConstrainEdge
--- value
---@field left NodeID
---@field rel SubtypeRelation
---@field shallowest_block integer
--- use
---@field right NodeID
---@field cause constraintcause

---@class LeftCallEdge
---@field left NodeID
---@field arg flex_value
---@field rel SubtypeRelation
---@field shallowest_block integer
---@field right NodeID
---@field cause constraintcause

---@class RightCallEdge
---@field left NodeID
---@field rel SubtypeRelation
---@field shallowest_block integer
---@field right NodeID
---@field arg flex_value
---@field cause constraintcause

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
	U.invalidate(self)
end

function Reachability:revert()
	self.constrain_edges:revert()
	self.leftcall_edges:revert()
	self.rightcall_edges:revert()
	U.invalidate(self)
end

---@enum TypeCheckerTag
local TypeCheckerTag = {
	VALUE = { VALUE = "VALUE" },
	USAGE = { USAGE = "USAGE" },
	METAVAR = { METAVAR = "METAVAR" },
	RANGE = { RANGE = "RANGE" },
}

---@alias ReachabilityQueue edgenotif[]

local function verify_tree(store, k1, k2)
	if type(store) == "table" then
		if U.is_invalid(store) then
			print("INVALID KEY: " .. tostring(k1) .. "\n parent: " .. tostring(k2))
			os.exit(-1, true)
			return false
		end

		if U.is_locked(store) then
			print(debug.traceback("LOCKED KEY: " .. tostring(k1) .. "\n parent: " .. tostring(k2)))
			os.exit(-1, true)
			return false
		end

		if getmetatable(store) and getmetatable(store).__length then
			if store[1] == nil then
				print("ARRAY DOESNT START AT 1: " .. tostring(k1))
				os.exit(-1, true)
			end
		end
		for k, v in pairs(store) do
			if k ~= "bindings" then
				if not verify_tree(v, k, k1) then
					return false
				end
			end
		end
	end

	return true
end

function TypeCheckerState:Snapshot()
	return {
		values = U.shallow_copy(self.values),
		constrain_edges = U.shallow_copy(self.graph.constrain_edges:all()),
		leftcall_edges = U.shallow_copy(self.graph.leftcall_edges:all()),
		rightcall_edges = U.shallow_copy(self.graph.rightcall_edges:all()),
	}
end

function TypeCheckerState:Visualize(diff1, diff2, restrict)
	local prev, cur
	if diff2 ~= nil then
		prev = diff1
		cur = diff2
	else
		prev = diff1
		cur = {
			values = self.values,
			constrain_edges = self.graph.constrain_edges:all(),
			leftcall_edges = self.graph.leftcall_edges:all(),
			rightcall_edges = self.graph.rightcall_edges:all(),
		}
	end

	local node_check = nil
	if restrict ~= nil then
		node_check = U.shallow_copy(restrict)

		local function propagate_edges(cur_edges, prev_edges)
			for i, e in ipairs(cur_edges) do
				if restrict[e.left] ~= nil or restrict[e.right] ~= nil then
					if
						not prev_edges
						or (prev_edges[i] and prev_edges[i].left == e.left and prev_edges[i].right == e.right)
					then
						node_check[e.left] = e.left
						node_check[e.right] = e.right
					end
				end
			end
		end

		if prev then
			propagate_edges(cur.constrain_edges, prev.constrain_edges)
			propagate_edges(cur.leftcall_edges, prev.leftcall_edges)
			propagate_edges(cur.rightcall_edges, prev.rightcall_edges)
		else
			propagate_edges(cur.constrain_edges, nil)
			propagate_edges(cur.leftcall_edges, nil)
			propagate_edges(cur.rightcall_edges, nil)
		end
	end

	local additions = {}
	local g = "digraph State {"

	for i, v in ipairs(cur.values) do
		local changed = true

		if prev and prev.values[i] then
			if node_check ~= nil and node_check[i] == nil then
				goto continue
			end

			changed = false
		else
			U.append(additions, i)
		end

		local label = U.strip_ansi(v[1]:pretty_print(v[3]))
		if #label > 800 then
			local i = 800
			-- Don't slice a unicode character in half
			while string.byte(label, i) > 127 do
				i = i + 1
			end
			label = label:sub(1, i)
		end

		--local s = label .. "\\n"
		--label = {}
		--for m in s:gmatch("(.-)\\n") do
		--[[while #m > 50 do
				local i = 50
				-- Don't slice a unicode character in half
				while string.byte(m, i) > 127 do
					i = i + 1
				end
				label = label .. m:sub(1, i) .. "\\n"
				m = m:sub(i + 1)
			end]]
		--U.append(label, m)
		--end
		--label = table.concat(label, "\\l")
		--label = label .. "\nCTX: " .. v[3]:format_names()
		label = label:gsub("\n", "\\n"):gsub('"', "'"):gsub("\\", "\\\\"):gsub("\\\\n", "\\l")
		local line = "\n" .. i .. " ["

		if not changed then
			line = line .. 'fontcolor="#cccccc", color="#cccccc", '
		end

		if v[1]:is_enum_value() and v[1]:unwrap_enum_value() == "empty" then
			line = line .. "shape=doubleoctagon]"
			g = g .. line
			goto continue
		elseif
			v[1]:is_stuck()
			and v[1]:unwrap_stuck():is_free()
			and v[1]:unwrap_stuck():unwrap_free():is_metavariable()
		then
			line = line .. "shape=doublecircle]"
			g = g .. line
			goto continue
		elseif v[1]:is_star() then
			line = line .. "shape=egg, "
		else
			line = line .. "shape=rect, "
		end

		g = g .. line .. 'label = "#' .. i .. " " .. label .. '"]'
		-- load-bearing no-op
		if true then
		end
		::continue::
	end

	for i, e in ipairs(cur.constrain_edges) do
		local line = "\n" .. e.left .. " -> " .. e.right .. " [arrowtail=inv,arrowhead=normal,dir=both"

		if
			prev
			and prev.constrain_edges[i]
			and prev.constrain_edges[i].left == e.left
			and prev.constrain_edges[i].right == e.right
		then
			if restrict ~= nil and restrict[e.left] == nil and restrict[e.right] == nil then
				goto continue2
			end
			line = line .. ', fontcolor="#cccccc", color="#cccccc"'
		end

		if e.rel.debug_name then
			local name = e.rel.debug_name
			if e.rel.debug_name == "UniverseOmegaRelation" then
				name = "< Ω :"
			end

			line = line .. ', label="' .. name .. '"'
		end

		g = g .. line .. "]"
		-- load-bearing no-op
		if true then
		end
		::continue2::
	end

	for i, e in ipairs(cur.leftcall_edges) do
		local line = "\n" .. e.left .. " -> " .. e.right .. " [arrowtail=invempty,arrowhead=normal,dir=both"

		if
			prev
			and prev.leftcall_edges[i]
			and prev.leftcall_edges[i].left == e.left
			and prev.leftcall_edges[i].right == e.right
		then
			if restrict ~= nil and restrict[e.left] == nil and restrict[e.right] == nil then
				goto continue3
			end
			line = line .. ', color="#cccccc"'
		end
		g = g .. line .. "]"
		-- load-bearing no-op
		if true then
		end
		::continue3::
	end

	for i, e in ipairs(cur.rightcall_edges) do
		local line = "\n" .. e.left .. " -> " .. e.right .. " [arrowtail=inv,arrowhead=empty,dir=both"

		if
			prev
			and prev.rightcall_edges[i]
			and prev.rightcall_edges[i].left == e.left
			and prev.rightcall_edges[i].right == e.right
		then
			if restrict ~= nil and restrict[e.left] == nil and restrict[e.right] == nil then
				goto continue4
			end
			line = line .. ', color="#cccccc"'
		end
		g = g .. line .. "]"
		-- load-bearing no-op
		if true then
		end
		::continue4::
	end

	return g .. "\n}", additions
end

function TypeCheckerState:DEBUG_VERIFY_TREE()
	return verify_tree(self.graph.constrain_edges._index_store)
end

function TypeCheckerState:DEBUG_VERIFY()
	self:DEBUG_VERIFY_TREE()
	self:DEBUG_VERIFY_VALUES()

	-- all nodes must be unique (no two nodes can have the same value, using the basic equality comparison on that value via ==)
	local unique = {}
	local transitive = {}

	for _, v in ipairs(self.graph.constrain_edges:all()) do
		if v.left == v.right then
			debug.traceback("INVALID CONSTRAINT!")
			os.exit(-1, true)
		end
		transitive[v.left + bit.lshift(v.right, 24)] = v -- bitshift by 24 via multiplication
	end

	for _, v in ipairs(self.pending) do
		if v:is_Constrain() then
			local left, rel, right, shallowest_block, item_cause = v:unwrap_Constrain()
			transitive[left + bit.lshift(right, 24)] = v
		end
	end

	for i, v in ipairs(self.values) do
		if v[2] == TypeCheckerTag.METAVAR then
			if
				v[1]:is_stuck()
				and v[1]:unwrap_stuck():is_free()
				and v[1]:unwrap_stuck():unwrap_free():is_metavariable()
			then
				if unique[v[1]] then
					print(
						debug.traceback(
							tostring(i)
								.. ": "
								.. tostring(self.values[i][1])
								.. " is a duplicate of "
								.. tostring(unique[v[1]])
								.. ": "
								.. tostring(v[1])
						)
					)
					os.exit(-1, true)
					return false
				end

				-- transitivity across metavariables (for every node that is a metavariable, there must exist some ConstraintEdge where .left is equal to the constraint to mv.value and .right is equal to the constraint for mv.usage)
				--    At all times, this must true across the graph, or constraints that would satisfy it must exist in the pending queue.
				local mv = v[1]:unwrap_stuck():unwrap_free():unwrap_metavariable()

				local from = self.graph.constrain_edges:to(mv.value) -- This looks at all constrains going "to" mv.value, but we begin our search here, so for us it is "from"
				local to = self.graph.constrain_edges:from(mv.usage) -- and vice-versa for here

				for _, f in ipairs(from) do
					for _, t in ipairs(to) do
						-- Find a constraint from f.left to t.right
						local l = f.left
						local r = t.right

						if transitive[l + bit.lshift(r, 24)] == nil then
							print(
								debug.traceback(
									tostring(i)
										.. " IS NOT TRANSITIVE! No constraint edge has left "
										.. tostring(l)
										.. " and right "
										.. tostring(r)
										.. " while looking at "
										.. tostring(f.left)
										.. ", "
										.. tostring(f.right)
										.. ", "
										.. tostring(t.left)
										.. ", "
										.. tostring(t.right)
										.. ", "
								)
							)
							os.exit(-1, true)
							return false
						end
					end
				end

				unique[v[1]] = i
			else
				print(
					debug.traceback(tostring(i) .. " is marked as a metavariable, but instead found " .. tostring(v[1]))
				)
				os.exit(-1, true)
				return false
			end
		end
	end

	if #self.pending == 0 then
		-- once the graph is settled, if a concrete_head to concrete_head path exists, then after completing flow(), it must have been discharged (this requires adding a "discharged" tracker that is set to true if the edge is passed to check_concrete or has the "constrain transitivity rule" applied to it. If at any time the graph has 0 pending operations, ALL edges must have a discharged value of true.)
	end

	return true
end

---check for combinations of constrain edges that induce new constraints in response to a constrain edges
---@param edge ConstrainEdge
---@param edge_id integer
---@param queue ReachabilityQueue
function Reachability:constrain_transitivity(edge, edge_id, queue)
	for i, l2 in ipairs(self.constrain_edges:to(edge.left)) do
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
				compositecause("composition", i, l2, edge_id, edge, U.anchor_here())
			)
		)
	end
	for i, r2 in ipairs(self.constrain_edges:from(edge.right)) do
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
				compositecause("composition", edge_id, edge, i, r2, U.anchor_here())
			)
		)
	end
end

function verify_collection(collection)
	for _, v in pairs(collection._index_store) do
		U.check_locked(v)
	end
end

---@param left integer
---@param right integer
---@param rel SubtypeRelation
---@param shallowest_block integer
---@param cause constraintcause
---@return integer?
function Reachability:add_constrain_edge(left, right, rel, shallowest_block, cause)
	if type(left) ~= "number" then
		error("left isn't an integer!")
	end
	if type(right) ~= "number" then
		error("right isn't an integer!")
	end

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
		return nil
	end

	---@type ConstrainEdge
	local edge = { left = left, right = right, rel = rel, shallowest_block = shallowest_block, cause = cause }
	return self.constrain_edges:add(edge)
end

---@param left integer
---@param arg flex_value
---@param rel SubtypeRelation
---@param right integer
---@param shallowest_block integer
---@param cause constraintcause
---@return integer?
function Reachability:add_call_left_edge(left, arg, rel, right, shallowest_block, cause)
	if type(left) ~= "number" then
		error("left isn't an integer!")
	end
	if type(right) ~= "number" then
		error("right isn't an integer!")
	end

	for _, edge in ipairs(self.leftcall_edges:between(left, right)) do
		if rel == edge.rel and arg == edge.arg then
			return nil
		end
	end
	---@type LeftCallEdge
	local edge = {
		left = left,
		arg = arg,
		rel = rel,
		right = right,
		shallowest_block = shallowest_block,
		cause = cause,
	}

	return self.leftcall_edges:add(edge)
end

---@param left integer
---@param rel SubtypeRelation
---@param right integer
---@param arg flex_value
---@param shallowest_block integer
---@param cause constraintcause
---@return integer?
function Reachability:add_call_right_edge(left, rel, right, arg, shallowest_block, cause)
	if type(left) ~= "number" then
		error("left isn't an integer!")
	end
	if type(right) ~= "number" then
		error("right isn't an integer!")
	end

	for _, edge in ipairs(self.rightcall_edges:between(left, right)) do
		if rel == edge.rel and arg == edge.arg then
			return nil
		end
	end
	---@type RightCallEdge
	local edge = {
		left = left,
		arg = arg,
		rel = rel,
		right = right,
		shallowest_block = shallowest_block,
		cause = cause,
	}

	return self.rightcall_edges:add(edge)
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

---@param l_ctx TypecheckingContext
---@param val flex_value
---@param use flex_value
---@param r_ctx TypecheckingContext
---@param cause any
function TypeCheckerState:queue_subtype(l_ctx, val, r_ctx, use, cause)
	local l = self:check_value(val, TypeCheckerTag.VALUE, l_ctx)
	local r = self:check_value(use, TypeCheckerTag.USAGE, r_ctx)
	--[[local l = U.tag(
		"check_value",
		{ val = val:pretty_preprint(l_ctx), use = use:pretty_preprint(r_ctx) },
		self.check_value,
		self,
		val,
		TypeCheckerTag.VALUE,
		l_ctx
	)
	local r = U.tag(
		"check_value",
		{ val = val:pretty_preprint(l_ctx), use = use:pretty_preprint(r_ctx) },
		self.check_value,
		self,
		use,
		TypeCheckerTag.USAGE,
		r_ctx
	)]]
	if type(l) ~= "number" then
		error("l isn't number, instead found " .. tostring(l))
	end
	if type(r) ~= "number" then
		error("r isn't number, instead found " .. tostring(r))
	end
	U.append(self.pending, EdgeNotif.Constrain(l, UniverseOmegaRelation, r, self.block_level, cause))
end

---@param l_ctx TypecheckingContext
---@param val flex_value
---@param rel SubtypeRelation
---@param r_ctx TypecheckingContext
---@param use flex_value
---@param cause any
function TypeCheckerState:queue_constrain(l_ctx, val, rel, r_ctx, use, cause)
	local l = self:check_value(val, TypeCheckerTag.VALUE, l_ctx)
	local r = self:check_value(use, TypeCheckerTag.USAGE, r_ctx)
	--[[local l = U.tag(
		"check_value",
		{ val = val:pretty_preprint(l_ctx), use = use:pretty_preprint(r_ctx) },
		self.check_value,
		self,
		val,
		TypeCheckerTag.VALUE,
		l_ctx
	)
	local r = U.tag(
		"check_value",
		{ val = val:pretty_preprint(l_ctx), use = use:pretty_preprint(r_ctx) },
		self.check_value,
		self,
		use,
		TypeCheckerTag.USAGE,
		r_ctx
	)]]
	if type(l) ~= "number" then
		error("l isn't number, instead found " .. tostring(l))
	end
	if type(r) ~= "number" then
		error("r isn't number, instead found " .. tostring(r))
	end
	U.append(self.pending, EdgeNotif.Constrain(l, rel, r, self.block_level, cause))
end

---@param l_ctx TypecheckingContext
---@param val flex_value
---@param rel SubtypeRelation
---@param r_ctx TypecheckingContext
---@param use flex_value
---@param cause any
---@return boolean, string?
function TypeCheckerState:send_constrain(l_ctx, val, rel, r_ctx, use, cause)
	if #self.pending == 0 then
		return self:constrain(val, l_ctx, use, r_ctx, rel, cause)
	else
		self:queue_constrain(l_ctx, val, rel, r_ctx, use, cause)
		return true
	end
end

---@param v flex_value
---@param tag TypeCheckerTag
---@param context TypecheckingContext
---@return NodeID
function TypeCheckerState:check_value(v, tag, context)
	if not v then
		error("nil passed into check_value!")
	end
	if not flex_value.value_check(v) then
		error("Must pass a flex_value into check_value! (Did you pass a strict or stuck value?)")
	end
	if context == nil then
		error("nil context passed into check_value! " .. debug.traceback())
	end
	--terms.verify_placeholders(v, context, self.values)
	verify_placeholder_lite(v, context)

	if v:is_stuck() and v:unwrap_stuck():is_free() and v:unwrap_stuck():unwrap_free():is_metavariable() then
		local mv = v:unwrap_stuck():unwrap_free():unwrap_metavariable()
		if tag == TypeCheckerTag.VALUE then
			if mv.value == nil then
				error("wtf")
			end
			return mv.value
		else
			if mv.usage == nil then
				error("wtf")
			end
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
			print("LOST CONSTRAINT")
			self:queue_constrain(
				context,
				bound,
				relation:unwrap_host_value(),
				context,
				v,
				terms.constraintcause.lost("range unpacking", U.strip_ansi(debug.traceback()))
			)
		end

		for _, bound in ipairs(upper_bounds) do
			print("LOST CONSTRAINT")
			self:queue_constrain(
				context,
				v,
				relation:unwrap_host_value(),
				context,
				bound,
				terms.constraintcause.lost("range_unpacking", U.strip_ansi(debug.traceback()))
			)
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
	if context == nil then
		error("nil context passed into metavariable! You can't do that anymore!!!")
	end
	local i = #self.values + 1
	local mv = setmetatable(
		-- block level here should probably be inside the context and not inside the metavariable
		{ value = i, usage = i, trait = trait or false, block_level = self.block_level, trace = U.bound_here(2) },
		terms.metavariable_mt
	)
	U.append(self.values, { mv:as_flex(), TypeCheckerTag.METAVAR, context })
	return mv
end

---@param val flex_value
---@param val_context TypecheckingContext
---@param use flex_value
---@param use_context TypecheckingContext
---@param cause constraintcause
---@return boolean
---@return string? error
function TypeCheckerState:flow(val, val_context, use, use_context, cause)
	if not flex_value.value_check(val) then
		error("val isn't a flex_value in flow()! (Did you pass a strict or stuck value?)")
	end
	if not flex_value.value_check(use) then
		error("use isn't a flex_value in flow()! (Did you pass a strict or stuck value?)")
	end
	--terms.verify_placeholders(val, val_context, self.values)
	--terms.verify_placeholders(use, use_context, self.values)
	local r = { self:constrain(val, val_context, use, use_context, UniverseOmegaRelation, cause) }

	if self.snapshot_count ~= nil then
		self.snapshot_index = ((self.snapshot_index or -1) + 1) % self.snapshot_count
		self.snapshot_buffer[self.snapshot_index + 1] = self:Snapshot()
	end

	return table.unpack(r)
end

---@param left integer
---@param right integer
---@param rel SubtypeRelation
---@param cause constraintcause
---@return boolean, string?
function TypeCheckerState:check_heads(left, right, rel, cause, ambient_typechecking_context)
	local l_value, ltag, l_ctx = table.unpack(self.values[left])
	local r_value, rtag, r_ctx = table.unpack(self.values[right])

	if ltag == TypeCheckerTag.VALUE and rtag == TypeCheckerTag.USAGE then
		if l_value:is_stuck() and l_value:unwrap_stuck():is_application() then
			return true
		end
		if r_value:is_stuck() and r_value:unwrap_stuck():is_application() then
			return true
		end
		-- Unpacking tuples hasn't been fixed in VSCode yet (despite the issue being closed???) so we have to override the types: https://github.com/LuaLS/lua-language-server/issues/1816
		local tuple_params = flex_value_array(
			flex_value.host_value(l_ctx),
			flex_value.host_value(l_value),
			flex_value.host_value(r_ctx),
			flex_value.host_value(r_value),
			flex_value.host_value(cause)
		)

		return apply_value(flex_value.strict(rel.constrain), flex_value.tuple_value(tuple_params), ambient_typechecking_context)
			:unwrap_host_tuple_value()
			:unpack()

		--[[U.tag("apply_value", {
			l_value = l_value:pretty_preprint(l_ctx),
			r_value = r_value:pretty_preprint(r_ctx),
			block_level = typechecker_state.block_level,
			rel = rel.debug_name,
			cause = cause,
		}, apply_value, rel.constrain, flex_value.tuple_value(tuple_params))]]
	end

	return true
end

---@param edge ConstrainEdge
---@param rel SubtypeRelation
function TypeCheckerState:constrain_induce_call(edge, rel)
	---@type flex_value, TypeCheckerTag, TypecheckingContext
	local l_value, ltag, l_ctx = table.unpack(self.values[edge.left])
	---@type flex_value, TypeCheckerTag, TypecheckingContext
	local r_value, rtag, r_ctx = table.unpack(self.values[edge.right])

	if --[[ltag == TypeCheckerTag.METAVAR and]]
		l_value:is_stuck() and l_value:unwrap_stuck():is_application()
	then
		local f, arg = l_value:unwrap_stuck():unwrap_application()
		local l = self:check_value(flex_value.stuck(f), TypeCheckerTag.VALUE, l_ctx)
		U.append(
			self.pending,
			EdgeNotif.CallLeft(
				l,
				arg,
				rel,
				edge.right,
				self.block_level,
				nestcause(
					"Inside constrain_induce_call ltag (maybe wrong constrain type?)",
					edge.cause,
					flex_value.stuck(f),
					r_value,
					l_ctx,
					r_ctx
				)
			)
		)
	end

	if --[[rtag == TypeCheckerTag.METAVAR and]]
		r_value:is_stuck() and r_value:unwrap_stuck():is_application()
	then
		local f, arg = r_value:unwrap_stuck():unwrap_application()
		local r = self:check_value(flex_value.stuck(f), TypeCheckerTag.USAGE, r_ctx)
		U.append(
			self.pending,
			EdgeNotif.CallRight(
				edge.left,
				rel,
				r,
				arg,
				self.block_level,
				nestcause(
					"Inside constrain_induce_call rtag (maybe wrong constrain type?)",
					edge.cause,
					l_value,
					flex_value.stuck(f),
					l_ctx,
					r_ctx
				)
			)
		)
	end
end

---check for compositions of a constrain edge and a left call edge in response to a new constrain edge
---@param edge ConstrainEdge
---@param edge_id integer
function TypeCheckerState:constrain_leftcall_compose_1(edge, edge_id)
	local mvalue, mtag, mctx = table.unpack(self.values[edge.right])
	if mtag == TypeCheckerTag.METAVAR then
		for i, r2 in ipairs(self.graph.leftcall_edges:from(edge.right)) do
			if FunctionRelation(r2.rel) ~= edge.rel then
				error(
					"Relations do not match! " .. tostring(FunctionRelation(r2.rel)) .. " is not " .. tostring(edge.rel)
				)
			end

			local l_value, _, l_ctx = table.unpack(self.values[edge.left])
			local l = self:check_value(apply_value(l_value, r2.arg, l_ctx), TypeCheckerTag.VALUE, l_ctx)
			U.append(
				self.pending,
				EdgeNotif.Constrain(
					l,
					r2.rel,
					r2.right,
					math.min(edge.shallowest_block, r2.shallowest_block),
					compositecause("leftcall_discharge", i, r2, edge_id, edge, U.anchor_here())
				)
			)
		end
	end
end

--- Check for a meet between a left call and a right call - if they have the same argument, induce a constraint between them
---@param edge LeftCallEdge
---@param edge_id integer
function TypeCheckerState:constrain_on_left_meet(edge, edge_id)
	for i, r in ipairs(self.graph.rightcall_edges:to(edge.left)) do
		if r.arg == edge.arg then
			-- Add constraint
			if r.rel ~= edge.rel then
				error("Relations do not match! " .. tostring(r.rel.Rel) .. " is not " .. tostring(edge.rel.Rel))
			end

			U.append(
				self.pending,
				EdgeNotif.Constrain(
					r.left,
					edge.rel,
					edge.right,
					math.min(edge.shallowest_block, r.shallowest_block),
					compositecause("composition", i, r, edge_id, edge, U.anchor_here())
				)
			)
		end
	end
end

--- Check for a meet between a right call and a left call - if they have the same argument, induce a constraint between them
---@param edge RightCallEdge
---@param edge_id integer
function TypeCheckerState:constrain_on_right_meet(edge, edge_id)
	for i, l in ipairs(self.graph.leftcall_edges:from(edge.right)) do
		if l.arg == edge.arg then
			-- Add constraint
			if l.rel ~= edge.rel then
				error("Relations do not match! " .. tostring(l.rel.Rel) .. " is not " .. tostring(edge.rel.Rel))
			end

			U.append(
				self.pending,
				EdgeNotif.Constrain(
					edge.left,
					edge.rel,
					l.right,
					math.min(edge.shallowest_block, l.shallowest_block),
					compositecause("composition", edge_id, edge, i, l, U.anchor_here())
				)
			)
		end
	end
end

---check for compositions of a constrain edge and a left call edge in response to a new left call edge
---@param edge LeftCallEdge
---@param edge_id integer
function TypeCheckerState:constrain_leftcall_compose_2(edge, edge_id)
	local mvalue, mtag, mctx = table.unpack(self.values[edge.left])
	if mtag == TypeCheckerTag.METAVAR then
		for i, l2 in ipairs(self.graph.constrain_edges:to(edge.left)) do
			if l2.rel ~= FunctionRelation(edge.rel) then
				error(
					"Relations do not match! " .. tostring(l2.rel) .. " is not " .. tostring(FunctionRelation(edge.rel))
				)
			end
			local l_value, _, l_ctx = table.unpack(self.values[l2.left])
			local new_value = apply_value(l_value, edge.arg, l_ctx)

			local l = self:check_value(new_value, TypeCheckerTag.VALUE, l_ctx)
			U.append(
				self.pending,
				EdgeNotif.Constrain(
					l,
					edge.rel,
					edge.right,
					math.min(edge.shallowest_block, l2.shallowest_block),
					compositecause("composition", i, l2, edge_id, edge, U.anchor_here())
				)
			)
		end
	end
end

---check for compositions of a right call edge and a constrain edge in response to a new constrain edge
---@param edge ConstrainEdge
---@param edge_id integer
function TypeCheckerState:rightcall_constrain_compose_2(edge, edge_id)
	local mvalue, mtag, mctx = table.unpack(self.values[edge.left])
	if mtag == TypeCheckerTag.METAVAR then
		for i, l2 in ipairs(self.graph.rightcall_edges:to(edge.left)) do
			if FunctionRelation(l2.rel) ~= edge.rel then
				error(
					"Relations do not match! " .. tostring(FunctionRelation(l2.rel)) .. " is not " .. tostring(edge.rel)
				)
			end
			local r_value, _, r_ctx = table.unpack(self.values[l2.left])
			local r = self:check_value(apply_value(r_value, l2.arg, r_ctx), TypeCheckerTag.VALUE, r_ctx)
			U.append(
				self.pending,
				EdgeNotif.Constrain(
					edge.left,
					l2.rel,
					r,
					math.min(edge.shallowest_block, l2.shallowest_block),
					compositecause("rightcall_discharge", edge_id, edge, i, l2, U.anchor_here())
				)
			)
		end
	end
end

---check for compositions of a right call edge and a constrain edge in response to a new right call edge
---@param edge RightCallEdge
---@param edge_id integer
function TypeCheckerState:rightcall_constrain_compose_1(edge, edge_id)
	local mvalue, mtag, mctx = table.unpack(self.values[edge.right])
	if mtag == TypeCheckerTag.METAVAR then
		for i, r2 in ipairs(self.graph.constrain_edges:from(edge.right)) do
			if r2.rel ~= FunctionRelation(edge.rel) then
				error(
					"Relations do not match! " .. tostring(r2.rel) .. " is not " .. tostring(FunctionRelation(edge.rel))
				)
			end
			local r_value, _, r_ctx = table.unpack(self.values[edge.left])
			local r = self:check_value(apply_value(r_value, edge.arg, r_ctx), TypeCheckerTag.VALUE, r_ctx)
			U.append(
				self.pending,
				EdgeNotif.Constrain(
					edge.left,
					edge.rel,
					r,
					math.min(edge.shallowest_block, r2.shallowest_block),
					compositecause("rightcall_discharge", i, r2, edge_id, edge, U.anchor_here())
				)
			)
		end
	end
end

function TypeCheckerState:DEBUG_VERIFY_VALUES()
	for i, v in ipairs(self.values) do
		terms.verify_placeholders(v[1], v[3], self.values)
	end
end

---@param val flex_value
---@param val_context TypecheckingContext
---@param use flex_value
---@param use_context TypecheckingContext
---@param rel SubtypeRelation
---@param cause constraintcause
---@return boolean
---@return string?
function TypeCheckerState:constrain(val, val_context, use, use_context, rel, cause)
	if not val then
		error("empty val passed into constrain!")
	end
	if not use then
		error("empty use passed into constrain!")
	end
	if #self.pending ~= 0 then
		error("pending not empty at start of constrain!")
	end
	--TODO: add contexts to queue_work if appropriate
	--self:queue_work(val, val_context, use, use_context, cause)

	self:queue_constrain(val_context, val, rel, use_context, use, cause)

	while #self.pending > 0 do
		--assert(self:DEBUG_VERIFY(), "VERIFICATION FAILED")
		local item = U.pop(self.pending)

		if item:is_Constrain() then
			local left, rel, right, shallowest_block, item_cause = item:unwrap_Constrain()
			local edge_id = self.graph:add_constrain_edge(left, right, rel, self.block_level, item_cause)

			if edge_id ~= nil then
				---@type ConstrainEdge
				local edge =
					{ left = left, rel = rel, right = right, shallowest_block = self.block_level, cause = item_cause }
				self.graph:constrain_transitivity(edge, edge_id, self.pending)
				local ok, err = self:check_heads(left, right, rel, item_cause, val_context)
				if not ok then
					if ok == nil then
						error(
							"check_head returned nil! Did you remember to return true from this relation? "
								.. tostring(rel)
						)
					end
					return ok, err
				end
				--[[U.tag(
					"check_heads",
					{ left = left, right = right, rel = rel.debug_name },
					self.check_heads,
					self,
					left,
					right,
					rel,
					item_cause
				)]]
				self:constrain_induce_call(edge, rel)
				self:constrain_leftcall_compose_1(edge, edge_id)
				self:rightcall_constrain_compose_2(edge, edge_id)
			end
		elseif item:is_CallLeft() then
			local left, arg, rel, right, shallowest_block, item_cause = item:unwrap_CallLeft()

			local edge_id = self.graph:add_call_left_edge(left, arg, rel, right, self.block_level, item_cause)

			if edge_id ~= nil then
				---@type LeftCallEdge
				local edge = {
					left = left,
					arg = arg,
					rel = rel,
					right = right,
					shallowest_block = self.block_level,
					cause = item_cause,
				}
				self:constrain_leftcall_compose_2(edge, edge_id)
				self:constrain_on_left_meet(edge, edge_id)
			end
		elseif item:is_CallRight() then
			local left, rel, right, arg, shallowest_block, item_cause = item:unwrap_CallRight()

			local edge_id = self.graph:add_call_right_edge(left, rel, right, arg, self.block_level, item_cause)
			if edge_id ~= nil then
				---@type RightCallEdge
				local edge = {
					left = left,
					rel = rel,
					right = right,
					arg = arg,
					shallowest_block = self.block_level,
					cause = item_cause,
				}
				self:rightcall_constrain_compose_1(edge, edge_id)
				self:constrain_on_right_meet(edge, edge_id) -- This just duplicates constrain_on_left_meet
			end
		else
			error("Unknown edge kind!")
		end
	end

	--assert(self:DEBUG_VERIFY(), "VERIFICATION FAILED")
	if #self.pending ~= 0 then
		error("pending was not drained!")
	end
	return true
end

---extract a region of a graph based on the block depth around a metavariable, for use in substitution
---@param mv Metavariable
---@param mappings {[integer]: typed} the placeholder we are trying to get rid of by substituting
---@param context_len integer number of bindings in the runtime context already used - needed for closures
---@param ambient_typechecking_context TypecheckingContext ambient context for resolving placeholders
---@return typed
function TypeCheckerState:slice_constraints_for(mv, mappings, context_len, ambient_typechecking_context)
	-- take only the constraints that are against this metavariable in such a way that it remains valid as we exit the block
	-- if the metavariable came from a "lower" block it is still in scope and may gain additional constraints in the future
	-- because this metavariable is from an outer scope, it doesn't have any constraints against something that is in the deeper scope and needs to be substituted,
	-- so we want to NOT include anything on the deeper side of a constraint towards this metavariable

	-- left is tail, right is head
	-- things flow ltr
	-- values flow to usages

	local constraints = array(terms.constraintelem)()

	---@param id integer
	---@return flex_value
	local function getnode(id)
		return self.values[id][1]
	end
	---@param id integer
	---@return TypecheckingContext
	local function getctx(id)
		return self.values[id][3]
	end

	---@generic T
	---@param edgeset T[]
	---@param extractor fun(edge: T) : integer
	---@param callback fun(edge: T)
	local function slice_edgeset(edgeset, extractor, callback)
		for _, edge in ipairs(edgeset) do
			local tag = self.values[extractor(edge)][2]
			if tag == TypeCheckerTag.METAVAR then
				local mvo = getnode(extractor(edge))

				if
					mvo:is_stuck()
					and mvo:unwrap_stuck():is_free()
					and mvo:unwrap_stuck():unwrap_free():is_metavariable()
				then
					local mvo_inner = mvo:unwrap_stuck():unwrap_free():unwrap_metavariable()
					if mvo_inner.block_level < self.block_level then
						callback(edge)
					end
				else
					error "incorrectly labelled as a metavariable"
				end
			elseif tag ~= TypeCheckerTag.RANGE then
				callback(edge)
			end
		end
	end

	slice_edgeset(self.graph.constrain_edges:to(mv.usage), function(edge)
		return edge.left
	end, function(edge)
		constraints:append(
			terms.constraintelem.constrain_sliced(
				substitute_inner(getnode(edge.left), mappings, context_len, ambient_typechecking_context),
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
				substitute_inner(getnode(edge.right), mappings, context_len, ambient_typechecking_context),
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
				substitute_inner(getnode(edge.left), mappings, context_len, ambient_typechecking_context),
				getctx(edge.left),
				substitute_inner(edge.arg, mappings, context_len, ambient_typechecking_context),
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
				substitute_inner(edge.arg, mappings, context_len, ambient_typechecking_context),
				edge.rel,
				substitute_inner(getnode(edge.right), mappings, context_len, ambient_typechecking_context),
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
				substitute_inner(getnode(edge.left), mappings, context_len, ambient_typechecking_context),
				getctx(edge.left),
				edge.rel,
				substitute_inner(edge.arg, mappings, context_len, ambient_typechecking_context),
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
				substitute_inner(getnode(edge.right), mappings, context_len, ambient_typechecking_context),
				getctx(edge.right),
				substitute_inner(edge.arg, mappings, context_len, ambient_typechecking_context),
				edge.cause
			)
		)
	end)

	return typed.constrained_type(constraints, self.values[mv.usage][3])
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
	}, { __index = TypeCheckerState, __shadow = self, __depth = U.getshadowdepth(self) + 1 })
end

function TypeCheckerState:commit()
	U.commit(self.pending)
	self.graph:commit()
	getmetatable(self).__shadow.block_level = self.block_level
	U.commit(self.values)
	U.commit(self.valcheck)
	U.commit(self.usecheck)
	self.trait_registry:commit()
	U.invalidate(self)
end

function TypeCheckerState:revert()
	U.revert(self.pending)
	self.graph:revert()
	U.revert(self.values)
	U.revert(self.valcheck)
	U.revert(self.usecheck)
	self.trait_registry:revert()
	U.invalidate(self)
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

---@param cause constraintcause
---@return string[]
local function assemble_causal_chain(cause)
	---@param left constraintcause
	---@param right constraintcause
	---@return string[]
	local function merge_causal_chain(left, right)
		local chain = assemble_causal_chain(left)
		for _, v in ipairs(assemble_causal_chain(right)) do
			U.append(chain, v)
		end
		return chain
	end

	local g = typechecker_state.graph
	if cause:is_composition() then
		local left, right, pos = cause:unwrap_composition()
		return merge_causal_chain(g.constrain_edges:all()[left].cause, g.constrain_edges:all()[right].cause)
	elseif cause:is_leftcall_discharge() then
		local call, constraint, pos = cause:unwrap_leftcall_discharge()
		return merge_causal_chain(g.leftcall_edges:all()[call].cause, g.constrain_edges:all()[constraint].cause)
	elseif cause:is_rightcall_discharge() then
		local constraint, call, pos = cause:unwrap_rightcall_discharge()
		return merge_causal_chain(g.constrain_edges:all()[constraint].cause, g.rightcall_edges:all()[call].cause)
	elseif cause:is_nested() then
		local desc, inner = cause:unwrap_nested()
		local chain = assemble_causal_chain(inner)
		U.append(chain, desc)
		return chain
	elseif cause:is_primitive() then
		local desc, pos = cause:unwrap_primitive()
		return { desc }
	elseif cause:is_lost() then
		local desc, stacktrace, pos = cause:unwrap_lost()
		return { desc }
	end
end

---@param cause constraintcause
---@param side boolean
---@param list table[]
local function assemble_side_chain(cause, side, list)
	local g = typechecker_state.graph

	---@param left constraintcause
	---@param right constraintcause
	---@param desc string
	---@return string[]
	local function split_causal_chain(left, right, desc)
		if side then
			local l = g.constrain_edges:all()[left]
			assemble_side_chain(l.cause, side, list)
			U.append(
				list,
				{ desc = desc, val = typechecker_state.values[l.left][1], l_ctx = typechecker_state.values[l.left][3] }
			)
		else
			local r = g.constrain_edges:all()[right]
			U.append(list, {
				desc = desc,
				use = typechecker_state.values[r.right][1],
				r_ctx = typechecker_state.values[r.right][3],
			})
			assemble_side_chain(r.cause, side, list)
		end
	end

	if cause:is_composition() then
		local left, right, pos = cause:unwrap_composition()
		split_causal_chain(left, right, "composition")
	elseif cause:is_leftcall_discharge() then
		local call, constraint, pos = cause:unwrap_leftcall_discharge()
		split_causal_chain(call, constraint, "leftcall discharge")
	elseif cause:is_rightcall_discharge() then
		local constraint, call, pos = cause:unwrap_rightcall_discharge()
		split_causal_chain(constraint, call, "rightcall discharge")
	elseif cause:is_nested() then
		local desc, inner = cause:unwrap_nested()
		if side then
			assemble_side_chain(inner, side, list)
			U.append(list, { desc = desc, val = cause.val, l_ctx = cause.l_ctx })
			if cause.val == nil then
				print("NIL VAL!")
			end
		else
			U.append(list, { desc = desc, use = cause.use, r_ctx = cause.r_ctx })
			assemble_side_chain(inner, side, list)
		end
	elseif cause:is_primitive() then
		local desc, pos = cause:unwrap_primitive()
		if side then
			U.append(list, { desc = desc, val = cause.val or "[<PRIMITIVE VAL>]", l_ctx = cause.l_ctx })
		else
			U.append(list, { desc = desc, use = cause.val or "[<PRIMITIVE USE>]", r_ctx = cause.r_ctx })
		end
	elseif cause:is_lost() then
		local desc, stacktrace, pos = cause:unwrap_lost()
		if side then
			U.append(list, { desc = desc, val = "[<LOST>]" })
		else
			U.append(list, { desc = desc, use = "[<LOST>]" })
		end
	end
end

terms.constraintcause.__tostring = function(self)
	--if self.track then
	local vals = {}
	local uses = {}
	assemble_side_chain(self, true, vals)
	assemble_side_chain(self, false, uses)
	local output = ""
	for _, v in ipairs(vals) do
		if v.desc then
			-- Note that ⟞↦ works better here but doesn't render well in the windows terminal, so we use ⊣→
			output = output .. "\n ⊣ " .. v.desc .. " → \n"
		else
			output = output .. "\n → \n"
		end
		if type(v.val) == "table" then
			output = output .. v.val:pretty_print(v.l_ctx)
			--if v.l_ctx then
			--	output = output .. "\nCONTEXT: " .. v.l_ctx:format_names()
			--end
		else
			output = output .. v.val
		end
	end
	output = output .. "\n : VAL → USE : \n"
	for _, v in ipairs(uses) do
		if type(v.use) == "table" then
			output = output .. v.use:pretty_print(v.r_ctx)
			--if v.r_ctx then
			--	output = output .. "\nCONTEXT: " .. v.r_ctx:format_names()
			--end
		else
			output = output .. v.use
		end
		if v.desc then
			output = output .. "\n ⊣ " .. v.desc .. " → \n"
		else
			output = output .. "\n → \n"
		end
	end
	return output
	--else
	--	local chain = assemble_causal_chain(self)
	--	return table.concat(chain, " → ")
	--end
end

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
	substitute_placeholders_identity = substitute_placeholders_identity,
	verify_placeholder_lite = verify_placeholder_lite,
}
internals_interface.evaluator = evaluator

---@generic T1, T2, T3, T4, T5, T6, T7, T8, T9
---@param fn fun() : boolean, T1?, T2?, T3?, T4?, T5?, T6?, T7?, T8?, T9?
---@return boolean, T1?, T2?, T3?, T4?, T5?, T6?, T7?, T8?, T9?
function TypeCheckerState:speculate(fn)
	typechecker_state = self:shadow()
	evaluator.typechecker_state = typechecker_state
	local r = { fn() }
	if r[1] then
		-- flattens all our changes back on to self
		typechecker_state:commit()
	else
		--print("REVERTING DUE TO: ", ...)
		typechecker_state:revert()
	end

	typechecker_state = self
	evaluator.typechecker_state = self
	return table.unpack(r)
end

return evaluator
