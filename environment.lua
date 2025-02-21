-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

local trie = require "lazy-prefix-tree"
local fibbuf = require "fibonacci-buffer"
local U = require "alicorn-utils"
local format = require "format"

local terms = require "terms"
local terms_gen = require "terms-generators"
local spanned_name, spanned_name_array = terms.spanned_name, terms.spanned_name_array
local unanchored_inferrable_term = terms.unanchored_inferrable_term
local anchored_inferrable_term = terms.anchored_inferrable_term
local typechecking_context = terms.typechecking_context
local module_mt = {}

local name_array = terms_gen.declare_array(terms_gen.builtin_string)

local evaluator = require "evaluator"
local infer = evaluator.infer

---@type table
local environment_mt

---Takes a table resembling an old environment (can be missing fields, it doesn't matter) and turns it into a new environment
---@param old_env { [string]: any }
---@param opts { [string]: any }?
---@return Environment
local function update_env(old_env, opts)
	---@type { [string]: any }
	local new_env = {}
	if opts then
		for k, v in pairs(opts) do
			new_env[k] = v
		end
	end
	if old_env then
		for k, v in pairs(old_env) do
			if new_env[k] == nil then
				new_env[k] = v
			end
		end
	end
	new_env.locals = new_env.locals or trie.empty
	new_env.nonlocals = new_env.nonlocals or trie.empty
	new_env.in_scope = new_env.nonlocals:extend(new_env.locals)
	new_env.bindings = new_env.bindings or fibbuf()
	new_env.purity = new_env.purity or terms.block_purity.pure
	new_env.perms = new_env.perms or {}
	new_env.typechecking_context = new_env.typechecking_context or typechecking_context()
	return setmetatable(new_env, environment_mt)
end

local new_env = update_env

---@class Environment
---@field typechecking_context TypecheckingContext
---@field locals PrefixTree
---@field nonlocals PrefixTree
---@field in_scope PrefixTree
---@field bindings FibonacciBuffer
---@field purity block_purity
---@field perms table
local environment = {}

---@class ShadowEnvironment
---@field shadowed Environment

---@param name string
---@return boolean
---@return anchored_inferrable|string
function environment:get(name)
	local present, binding = self.in_scope:get(name)
	if not present then
		return false, 'symbol "' .. name .. '" is not in scope'
	end
	if binding == nil then
		return false,
			'symbol "'
				.. name
				.. '" is marked as present but with no data; this indicates a bug in the environment or something violating encapsulation'
	end
	return true, binding
end

---@param name string
---@param type flex_value
---@param value flex_value
local function log_binding(name, type, value)
	print("New let binding")
	print("name:", name)
	print("type: (value term follows)")
	print(type)
	print("value: (value term follows)")
	print(value)
end

---@overload fun(binding: binding) : boolean, string
---@param binding binding
---@return boolean, Environment
function environment:bind_local(binding)
	--print("bind_local: (binding term follows)")
	--print(binding:pretty_print(self.typechecking_context))
	if not self.purity:is_pure() and not self.purity:is_effectful() then
		error("nyi environment dependent purity")
	end
	local typechecking_context = self.typechecking_context
	if binding:is_let() then
		local name, debuginfo, anchored_expr = binding:unwrap_let()
		local anchor, _ = anchored_expr:unwrap_anchored_inferrable()
		local ok, expr_type, expr_usages, expr_term = infer(anchored_expr, typechecking_context)
		if not ok then
			---@cast expr_type string
			return false, expr_type
		end
		---@cast expr_type -string
		if terms.flex_value.value_check(expr_type) ~= true then
			print("expr", expr)
			error("infer returned a bad type for expr in bind_local")
		end
		local n = typechecking_context:len()
		local term = anchored_inferrable_term(anchor, unanchored_inferrable_term.bound_variable(n + 1, debuginfo))
		local locals = self.locals:put(name, term)
		local evaled = evaluator.evaluate(expr_term, typechecking_context.runtime_context, typechecking_context)

		if terms.strict_value.value_check(evaled) then
			evaled = evaluator.evaluate(expr_term, typechecking_context.runtime_context, typechecking_context)
		end
		-- print "doing let binding"
		-- print(expr:pretty_print())
		--log_binding(name, expr_type, evaled)
		typechecking_context = typechecking_context:append(name, expr_type, evaled, debuginfo)
		local bindings = self.bindings:append(binding)
		return true,
			U.notail(update_env(self, {
				locals = locals,
				bindings = bindings,
				typechecking_context = typechecking_context,
			}))
	elseif binding:is_tuple_elim() then
		local names, infos, subject = binding:unwrap_tuple_elim()
		local anchor, _ = subject:unwrap_anchored_inferrable()
		local ok, subject_type, subject_usages, subject_term = infer(subject, typechecking_context)
		if not ok then
			---@cast subject_type string
			return false, subject_type
		end
		---@cast subject_type -string
		--local subject_qty, subject_type = subject_type:unwrap_qtype()
		--DEBUG:
		if subject_type:is_enum_value() then
			print("bad tuple subject infer")
			print(subject:pretty_print(typechecking_context))
		end

		local desc = terms.empty
		for _ in ipairs(names) do
			local next_elem_type_mv = evaluator.typechecker_state:metavariable(typechecking_context)
			local next_elem_type = next_elem_type_mv:as_flex()
			desc = terms.cons(desc, next_elem_type)
		end
		local spec_type = terms.flex_value.tuple_type(desc)
		local host_spec_type = terms.flex_value.host_tuple_type(desc)
		local function inner_tuple_elim(spec_type)
			local ok, err = evaluator.typechecker_state:speculate(function()
				return evaluator.typechecker_state:flow(
					subject_type,
					typechecking_context,
					spec_type,
					typechecking_context,
					terms.constraintcause.primitive("environment tuple-elim", format.anchor_here())
				)
			end)
			if not ok then
				return false, err
			end

			-- evaluating the subject is necessary for inferring the type of the body
			local subject_value =
				evaluator.evaluate(subject_term, typechecking_context:get_runtime_context(), typechecking_context)
			--[[local subject_value = U.tag(
				"evaluate",
				{ subject_term = subject_term:pretty_preprint(typechecking_context) },
				evaluator.evaluate,
				subject_term,
				typechecking_context:get_runtime_context()
			)]]
			-- extract subject type and evaled for each elem in tuple
			local tupletypes, n_elements = evaluator.infer_tuple_type(typechecking_context, spec_type, subject_value)

			--local desc
			--[[

			if inner_type:is_tuple_type() then
				desc = subject_type:unwrap_tuple_type()
			elseif inner_type:is_host_tuple_type() then
				desc = subject_type:unwrap_host_tuple_type()
			else
				error("bind_local tuple_elim, subject_type: expected a term with a tuple type, but got " .. subject_type.kind)
			end
			]]

			local n = typechecking_context:len()
			local locals = self.locals

			if not (n_elements == names:len()) then
				error("attempted to bind " .. n_elements .. " tuple elements to " .. names:len() .. " variables")
			end

			for i, v in ipairs(names) do
				--local constructor, arg = desc:unwrap_enum_value()
				-- if constructor ~= "cons" then
				-- 	error("todo: this error message")
				-- end
				local term =
					anchored_inferrable_term(anchor, unanchored_inferrable_term.bound_variable(n + i, infos[i]))
				locals = locals:put(v, term)

				local evaled = evaluator.index_tuple_value(subject_value, i)
				--log_binding(v, tupletypes[i], evaled)
				typechecking_context = typechecking_context:append(v, tupletypes[i], evaled, infos[i])
			end
			local bindings = self.bindings:append(binding)
			return true,
				U.notail(update_env(self, {
					locals = locals,
					bindings = bindings,
					typechecking_context = typechecking_context,
				}))
		end
		local ok, res1, res2
		ok, res1 = inner_tuple_elim(spec_type)
		if ok then
			return true, res1
		end
		ok, res2 = inner_tuple_elim(host_spec_type)
		if ok then
			return true, res2
		end
		--error(res1)
		--error(res2)
		-- try uncommenting one of the error prints above
		-- you need to figure out which one is relevant for your problem
		-- after you're finished, please comment it out so that, next time, the message below can be found again
		error("(binding) tuple elim speculation failed! debugging this is left as an exercise to the maintainer")
	elseif binding:is_record_elim() then
		local binding_anchor, subject, field_names, field_var_debugs = binding:unwrap_record_elim()
		local locals = self.locals
		local context_length = typechecking_context:len()
		for field_index, field_name in ipairs(field_names) do
			local field_var_debug = field_var_debugs[field_index]
			local field_var_name, field_var_anchor = field_var_debug:unwrap_spanned_name()
			local field_var_expr = anchored_inferrable_term(
				binding_anchor,
				unanchored_inferrable_term.record_elim(
					subject,
					name_array(field_name),
					spanned_name_array(field_var_debug),
					anchored_inferrable_term(
						field_var_anchor.start,
						unanchored_inferrable_term.bound_variable(context_length + 1, field_var_debug)
					)
				)
			)
			locals = locals:put(field_var_name, field_var_expr)
		end
		local bindings = self.bindings:append(binding)
		return true,
			U.notail(update_env(self, {
				locals = locals,
				bindings = bindings,
				typechecking_context = typechecking_context,
			}))
	elseif binding:is_annotated_lambda() then
		local param_name, param_annotation, start_anchor, visible = binding:unwrap_annotated_lambda()
		if not start_anchor or not start_anchor.id then
			print("binding", binding)
			error "missing start_anchor for annotated lambda binding"
		end
		local ok, annotation_type, annotation_usages, annotation_term = infer(param_annotation, typechecking_context)
		if not ok then
			---@cast annotation_type string
			return false, annotation_type
		end
		---@cast annotation_type -string
		--print("binding lambda annotation: (typed term follows)")
		--print(annotation_term:pretty_print(typechecking_context))
		local evaled = evaluator.evaluate(annotation_term, typechecking_context.runtime_context, typechecking_context)
		local bindings = self.bindings:append(binding)
		local info = spanned_name(param_name, start_anchor:span(start_anchor))
		local locals = self.locals:put(
			param_name,
			anchored_inferrable_term(
				start_anchor,
				unanchored_inferrable_term.bound_variable(typechecking_context:len() + 1, info)
			)
		)
		local typechecking_context = typechecking_context:append(param_name, evaled, nil, info)
		return true,
			U.notail(update_env(self, {
				locals = locals,
				bindings = bindings,
				typechecking_context = typechecking_context,
			}))
		--error "NYI lambda bindings"
	elseif binding:is_program_sequence() then
		if self.purity:is_pure() then
			error("binding.program_sequence is only allowed in effectful blocks")
		end
		local first, start_anchor = binding:unwrap_program_sequence()
		local ok, first_type, first_usages, first_term = infer(first, typechecking_context)
		if not ok then
			return false, first_type
		end

		local first_effect_type = evaluator.typechecker_state:metavariable(typechecking_context):as_flex()
		local first_result_type = evaluator.typechecker_state:metavariable(typechecking_context):as_flex()
		local ok, err = evaluator.typechecker_state:flow(
			first_type,
			typechecking_context,
			terms.flex_value.program_type(first_effect_type, first_result_type),
			typechecking_context,
			terms.constraintcause.primitive("Inferring on program type ", start_anchor)
		)
		if not ok then
			return false, err
		end

		--print("FOUND EFFECTFUL BINDING", first_result_type, "produced by ", first_type)
		local n = typechecking_context:len()
		local debuginfo = spanned_name("#program_sequence", start_anchor:span(start_anchor))
		local term = anchored_inferrable_term(start_anchor, unanchored_inferrable_term.bound_variable(n + 1, debuginfo))
		local locals = self.locals:put("#program-sequence", term)
		typechecking_context = typechecking_context:append("#program-sequence", first_result_type, nil, debuginfo)
		local bindings = self.bindings:append(binding)
		return true,
			U.notail(update_env(self, {
				locals = locals,
				bindings = bindings,
				typechecking_context = typechecking_context,
			}))
	else
		error("bind_local: unknown kind: " .. binding.kind)
	end
	error("unreachable!?")
end

---@class Module
---@field bindings PrefixTree

---@return Environment
---@return Module
function environment:gather_module()
	return self, setmetatable({ bindings = self.locals }, module_mt)
end

---@param module Module
---@return Environment
function environment:open_module(module)
	return U.notail(new_env({
		locals = self.locals:extend(module.bindings),
		nonlocals = self.nonlocals,
		perms = self.perms,
	}))
end

---@param module Module
---@return Environment
function environment:use_module(module)
	return U.notail(new_env({
		locals = self.locals,
		nonlocals = self.nonlocals:extend(module.bindings),
		perms = self.perms,
	}))
end

---@param name string
---@return Environment
function environment:unlet_local(name)
	return U.notail(new_env({
		locals = self.locals:remove(name),
		nonlocals = self.nonlocals,
		perms = self.perms,
	}))
end

---enter a new block, shadowing the current context and allowing new bindings
---@param purity block_purity
---@return ShadowEnvironment
---@return Environment
function environment:enter_block(purity)
	--print "entering block"
	--self.typechecking_context:dump_names()
	if purity:is_inherit() then
		purity = self.purity
	end
	evaluator.typechecker_state:enter_block()
	return { shadowed = self },
		U.notail(new_env({
			-- locals = nil,
			nonlocals = self.in_scope,
			purity = purity,
			perms = self.perms,
			typechecking_context = self.typechecking_context,
		}))
end

---exit a block, resolving the bindings in that block and restoring the shadowed locals
---@param term anchored_inferrable
---@param shadowed ShadowEnvironment
---@return Environment
---@return anchored_inferrable
---@return purity
function environment:exit_block(term, shadowed)
	-- -> env, term
	local purity
	if self.purity:is_pure() then
		purity = terms.purity.pure
	elseif self.purity:is_effectful() then
		purity = terms.purity.effectful
	else
		error("nyi environment dependent purity")
	end
	local outer = shadowed.shadowed or error "shadowed.shadowed missing"
	local env = new_env {
		locals = outer.locals,
		nonlocals = outer.nonlocals,
		in_scope = outer.in_scope,
		perms = outer.perms,
		typechecking_context = outer.typechecking_context,
		bindings = outer.bindings,
		purity = outer.purity,
	}
	--print("exiting block and dropping " .. #self.bindings .. " bindings")
	--self.typechecking_context:dump_names()
	--print "outer"
	--outer.typechecking_context:dump_names()
	--print "new"
	--env.typechecking_context:dump_names()

	---@type anchored_inferrable
	local wrapped = term
	local anchor, _ = term:unwrap_anchored_inferrable()
	if purity:is_effectful() then
		wrapped = anchored_inferrable_term(anchor, unanchored_inferrable_term.program_end(wrapped))
	end
	for idx = self.bindings:len(), 1, -1 do
		---@type binding
		local binding = self.bindings:get(idx)
		if not binding then
			error "missing binding"
		end
		---@type unanchored_inferrable
		local unanchored_wrapped
		if binding:is_let() then
			local name, debuginfo, expr = binding:unwrap_let() -- TODO: propagate anchors
			unanchored_wrapped = unanchored_inferrable_term.let(name, debuginfo, expr, wrapped)
		elseif binding:is_tuple_elim() then
			local names, debuginfo, subject = binding:unwrap_tuple_elim() -- TODO: propagate anchors
			unanchored_wrapped = unanchored_inferrable_term.tuple_elim(names, debuginfo, subject, wrapped)
		elseif binding:is_record_elim() then
			local _binding_anchor, subject, field_names, field_var_debugs = binding:unwrap_record_elim()
			unanchored_wrapped = unanchored_inferrable_term.record_elim(subject, field_names, field_var_debugs, wrapped)
		elseif binding:is_annotated_lambda() then
			local name, annotation, start_anchor, visible, pure = binding:unwrap_annotated_lambda()
			unanchored_wrapped =
				unanchored_inferrable_term.annotated_lambda(name, annotation, wrapped, start_anchor, visible, pure)
		elseif binding:is_program_sequence() then
			local first, start_anchor = binding:unwrap_program_sequence()
			unanchored_wrapped = unanchored_inferrable_term.program_sequence(
				first,
				start_anchor,
				wrapped,
				spanned_name("#program-sequence", start_anchor:span(start_anchor))
			)
		else
			error("exit_block: unknown kind: " .. binding.kind)
		end

		wrapped = anchored_inferrable_term(anchor, unanchored_wrapped)
	end
	evaluator.typechecker_state:exit_block()

	return env, wrapped, purity
end

environment_mt = {
	__index = environment,
	__tostring = function(s)
		return "[Environment Omitted]"
	end,
}

---@param env Environment
---@return string
local function dump_env(env)
	return "Environment" .. "\nlocals: " .. trie.dump_map(env.locals) .. "\nnonlocals: " .. trie.dump_map(env.nonlocals)
end

return {
	new_env = new_env,
	dump_env = dump_env,
}
