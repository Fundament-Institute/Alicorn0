local trie = require "lazy-prefix-tree"
local fibbuf = require "fibonacci-buffer"
local U = require "alicorn-utils"

local terms = require "terms"
local inferrable_term = terms.inferrable_term
local typechecking_context = terms.typechecking_context
local module_mt = {}

local evaluator = require "evaluator"
local infer = evaluator.infer

local environment_mt

---Takes a table resembling an old environment (can be missing fields, it doesn't matter) and turns it into a new environment
---@param old_env table
---@param opts table?
---@return Environment
local function update_env(old_env, opts)
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
---@return inferrable|string
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
---@param type value
---@param value value
local function log_binding(name, type, value)
	print("New let binding")
	print("name:", name)
	print("type: (value term follows)")
	print(type)
	print("value: (value term follows)")
	print(value)
end

---@param binding binding
---@return Environment
function environment:bind_local(binding)
	--print("bind_local: (binding term follows)")
	--print(binding:pretty_print(self.typechecking_context))
	if not self.purity:is_pure() and not self.purity:is_effectful() then
		error("nyi environment dependent purity")
	end
	if binding:is_let() then
		local name, expr = binding:unwrap_let()
		local expr_type, expr_usages, expr_term = infer(expr, self.typechecking_context)
		if terms.value.value_check(expr_type) ~= true then
			print("expr", expr)
			error("infer returned a bad type for expr in bind_local")
		end
		local n = self.typechecking_context:len()
		local term = inferrable_term.bound_variable(n + 1)
		local locals = self.locals:put(name, term)
		local evaled = evaluator.evaluate(expr_term, self.typechecking_context.runtime_context)
		-- print "doing let binding"
		-- print(expr:pretty_print())
		--log_binding(name, expr_type, evaled)
		local typechecking_context = self.typechecking_context:append(name, expr_type, evaled)
		local bindings = self.bindings:append(binding)
		return update_env(self, {
			locals = locals,
			bindings = bindings,
			typechecking_context = typechecking_context,
		})
	elseif binding:is_tuple_elim() then
		local names, subject = binding:unwrap_tuple_elim()
		local subject_type, subject_usages, subject_term = infer(subject, self.typechecking_context)
		--local subject_qty, subject_type = subject_type:unwrap_qtype()
		--DEBUG:
		if subject_type:is_enum_value() then
			print "bad subject infer"
			print(subject:pretty_print(self.typechecking_context))
		end

		local desc = terms.empty
		for _ in names:ipairs() do
			local next_elem_type_mv = evaluator.typechecker_state:metavariable(self.typechecking_context)
			local next_elem_type = next_elem_type_mv:as_value()
			desc = terms.cons(desc, next_elem_type)
		end
		local spec_type = terms.value.tuple_type(desc)
		local host_spec_type = terms.value.host_tuple_type(desc)
		local function rest_of_the_tuple_elim(spec_type)
			-- evaluator.typechecker_state:flow(
			-- 	subject_type,
			-- 	self.typechecking_context,
			-- 	spec_type,
			-- 	self.typechecking_context,
			-- 	"environment tuple-elim"
			-- )
			U.tag(
				"flow",
				{ subject_type = subject_type, spec_type = spec_type },
				evaluator.typechecker_state.flow,
				evaluator.typechecker_state,
				subject_type,
				self.typechecking_context,
				spec_type,
				self.typechecking_context,
				"environment tuple-elim"
			)

			-- evaluating the subject is necessary for inferring the type of the body
			local subject_value = U.tag(
				"evaluate",
				{ subject_term = subject_term },
				evaluator.evaluate,
				subject_term,
				self.typechecking_context:get_runtime_context()
			)
			-- extract subject type and evaled for each elem in tuple
			local tupletypes, n_elements = evaluator.infer_tuple_type(spec_type, subject_value)

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

			local typechecking_context = self.typechecking_context
			local n = typechecking_context:len()
			local locals = self.locals

			if not (n_elements == names:len()) then
				error("attempted to bind " .. n_elements .. " tuple elements to " .. names:len() .. " variables")
			end

			for i, v in names:ipairs() do
				--local constructor, arg = desc:unwrap_enum_value()
				-- if constructor ~= "cons" then
				-- 	error("todo: this error message")
				-- end
				local term = inferrable_term.bound_variable(n + i)
				locals = locals:put(v, term)

				local evaled = evaluator.index_tuple_value(subject_value, i)
				--log_binding(v, tupletypes[i], evaled)
				typechecking_context = typechecking_context:append(v, tupletypes[i], evaled)
			end
			local bindings = self.bindings:append(binding)
			return update_env(self, {
				locals = locals,
				bindings = bindings,
				typechecking_context = typechecking_context,
			})
		end
		local unique = {}
		local ok, res1, res2
		ok, res1 = evaluator.typechecker_state:speculate(function()
			return rest_of_the_tuple_elim(spec_type)
		end)
		-- local ok, res = U.tag(
		-- 	"speculate",
		-- 	{ unique = unique },
		-- 	evaluator.typechecker_state.speculate,
		-- 	evaluator.typechecker_state,
		-- 	function()
		-- 		return rest_of_the_tuple_elim(spec_type)
		-- 	end
		-- )
		if ok then
			return res1
		end
		ok, res2 = evaluator.typechecker_state:speculate(function()
			return rest_of_the_tuple_elim(host_spec_type)
		end)
		-- ok, res = U.tag(
		-- 	"speculate",
		-- 	{ unique = unique },
		-- 	evaluator.typechecker_state.speculate,
		-- 	evaluator.typechecker_state,
		-- 	function()
		-- 		return rest_of_the_tuple_elim(host_spec_type)
		-- 	end
		-- )
		if ok then
			return res2
		end
		-- error(res1)
		error(res2)
		error("tuple elim speculation failed! debugging this is left as an exercise to the maintainer")
	elseif binding:is_annotated_lambda() then
		local param_name, param_annotation, start_anchor, visible = binding:unwrap_annotated_lambda()
		if not start_anchor or not start_anchor.sourceid then
			print("binding", binding)
			error "missing start_anchor for annotated lambda binding"
		end
		local annotation_type, annotation_usages, annotation_term = infer(param_annotation, self.typechecking_context)
		--print("binding lambda annotation: (typed term follows)")
		--print(annotation_term:pretty_print(self.typechecking_context))
		local evaled = evaluator.evaluate(annotation_term, self.typechecking_context.runtime_context)
		local bindings = self.bindings:append(binding)
		local locals = self.locals:put(param_name, inferrable_term.bound_variable(self.typechecking_context:len() + 1))
		local typechecking_context = self.typechecking_context:append(param_name, evaled, nil, start_anchor)
		return update_env(self, {
			locals = locals,
			bindings = bindings,
			typechecking_context = typechecking_context,
		})
		--error "NYI lambda bindings"
	elseif binding:is_program_sequence() then
		if self.purity:is_pure() then
			error("binding.program_sequence is only allowed in effectful blocks")
		end
		local first, start_anchor = binding:unwrap_program_sequence()
		local first_type, first_usages, first_term = infer(first, self.typechecking_context)
		if not first_type:is_program_type() then
			error("program sequence must infer to a program type")
		end
		local first_effect_sig, first_base_type = first_type:unwrap_program_type()
		--print("FOUND EFFECTFUL BINDING", first_base_type, "produced by ", first_type)
		local n = self.typechecking_context:len()
		local term = inferrable_term.bound_variable(n + 1)
		local locals = self.locals:put("#program-sequence", term)
		local typechecking_context =
			self.typechecking_context:append("#program-sequence", first_base_type, nil, start_anchor)
		local bindings = self.bindings:append(binding)
		return update_env(self, {
			locals = locals,
			bindings = bindings,
			typechecking_context = typechecking_context,
		})
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
	return new_env {
		locals = self.locals:extend(module.bindings),
		nonlocals = self.nonlocals,
		perms = self.perms,
	}
end

---@param module Module
---@return Environment
function environment:use_module(module)
	return new_env {
		locals = self.locals,
		nonlocals = self.nonlocals:extend(module.bindings),
		perms = self.perms,
	}
end

---@param name string
---@return Environment
function environment:unlet_local(name)
	return new_env {
		locals = self.locals:remove(name),
		nonlocals = self.nonlocals,
		perms = self.perms,
	}
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
		new_env {
			-- locals = nil,
			nonlocals = self.in_scope,
			purity = purity,
			perms = self.perms,
			typechecking_context = self.typechecking_context,
		}
end

---exit a block, resolving the bindings in that block and restoring the shadowed locals
---@param term inferrable
---@param shadowed ShadowEnvironment
---@return Environment
---@return inferrable
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
	local wrapped = term
	if purity:is_effectful() then
		wrapped = terms.inferrable_term.program_end(wrapped)
	end
	for idx = self.bindings:len(), 1, -1 do
		---@type binding
		local binding = self.bindings:get(idx)
		if not binding then
			error "missing binding"
		end
		if binding:is_let() then
			local name, expr = binding:unwrap_let()
			wrapped = terms.inferrable_term.let(name, expr, wrapped)
		elseif binding:is_tuple_elim() then
			local names, subject = binding:unwrap_tuple_elim()
			wrapped = terms.inferrable_term.tuple_elim(names, subject, wrapped)
		elseif binding:is_annotated_lambda() then
			local name, annotation, start_anchor, visible, purity = binding:unwrap_annotated_lambda()
			wrapped = terms.inferrable_term.annotated_lambda(name, annotation, wrapped, start_anchor, visible, purity)
		elseif binding:is_program_sequence() then
			local first, start_anchor = binding:unwrap_program_sequence()
			wrapped = terms.inferrable_term.program_sequence(first, start_anchor, wrapped)
		else
			error("exit_block: unknown kind: " .. binding.kind)
		end
	end
	evaluator.typechecker_state:exit_block()

	return env, wrapped, purity
end

environment_mt = { __index = environment }

---@param env Environment
---@return string
local function dump_env(env)
	return "Environment" .. "\nlocals: " .. trie.dump_map(env.locals) .. "\nnonlocals: " .. trie.dump_map(env.nonlocals)
end

return {
	new_env = new_env,
	dump_env = dump_env,
}
