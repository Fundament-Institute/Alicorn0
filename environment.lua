local trie = require "./lazy-prefix-tree"
local fibbuf = require "./fibonacci-buffer"

local terms = require "./terms"
local inferrable_term = terms.inferrable_term
local typechecking_context = terms.typechecking_context
local module_mt = {}

local eval = require "./evaluator"
local infer = eval.infer

local environment_mt

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
	new_env.perms = new_env.perms or {}
	new_env.typechecking_context = new_env.typechecking_context or typechecking_context()
	return setmetatable(new_env, environment_mt)
end

local new_env = update_env

environment_mt = {
	__index = {
		get = function(self, name)
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
		end,
		bind_local = function(self, binding)
			p(binding)
			if binding:is_let() then
				local name, expr = binding:unwrap_let()
				local expr_type, expr_usages, expr_term = infer(expr, self.typechecking_context)
				local n = #self.typechecking_context
				local term = inferrable_term.bound_variable(n + 1)
				local locals = self.locals:put(name, term)
				local evaled = eval.evaluate(expr_term, self.typechecking_context.runtime_context)
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
				local subject_quantity, subject_type = subject_type:unwrap_qtype()

				-- evaluating the subject is necessary for inferring the type of the body
				local subject_value = eval.evaluate(subject_term, self.typechecking_context:get_runtime_context())
				-- extract subject type and evaled for each elem in tuple
				local tupletypes, n_elements = eval.infer_tuple_type(subject_type, subject_value)

				local decls

				if subject_type:is_tuple_type() then
					decls = subject_type:unwrap_tuple_type()
				elseif subject_type:is_prim_tuple_type() then
					decls = subject_type:unwrap_prim_tuple_type()
				end

				local typechecking_context = self.typechecking_context
				local n = #typechecking_context
				local locals = self.locals

				if not (n_elements == #names) then
					error("attempted to bind " .. n_elements .. " tuple elements to " .. #names .. " variables")
				end

				for i, v in ipairs(names) do
					local constructor, arg = decls:unwrap_enum_value()
					if constructor ~= "cons" then
						error("todo: this error message")
					end
					local term = inferrable_term.bound_variable(n + i)
					locals = locals:put(v, term)
					typechecking_context = typechecking_context:append(v, tupletypes[i])
				end
				local bindings = self.bindings:append(binding)
				return update_env(self, {
					locals = locals,
					bindings = bindings,
					typechecking_context = typechecking_context,
				})
			elseif binding:is_annotated_lambda() then
				local param_name, param_annotation = binding:unwrap_annotated_lambda()
				local annotation_type, annotation_usages, annotation_term =
					infer(param_annotation, self.typechecking_context)
				local evaled = eval.evaluate(annotation_term, self.typechecking_context.runtime_context)
				error "NYI lambda bindings"
			else
				error("bind_local: unknown kind: " .. binding.kind)
			end
			error("unreachable!?")
		end,
		gather_module = function(self)
			return self, setmetatable({ bindings = self.locals }, module_mt)
		end,
		open_module = function(self, module)
			return new_env {
				locals = self.locals:extend(module.bindings),
				nonlocals = self.nonlocals,
				perms = self.perms,
			}
		end,
		use_module = function(self, module)
			return new_env {
				locals = self.locals,
				nonlocals = self.nonlocals:extend(module.bindings),
				perms = self.perms,
			}
		end,
		unlet_local = function(self, name)
			return new_env {
				locals = self.locals:remove(name),
				nonlocals = self.nonlocals,
				perms = self.perms,
			}
		end,
		enter_block = function(self)
			return { shadowed = self },
				new_env {
					-- locals = nil,
					nonlocals = self.nonlocals:extend(self.locals),
					perms = self.perms,
				}
		end,
		child_scope = function(self)
			return new_env {
				locals = trie.empty,
				nonlocals = self.bindings,
				perms = self.perms,
			}
		end,
		exit_child_scope = function(self, child)
			return new_env {
				locals = self.locals,
				nonlocals = self.nonlocals,
				perms = self.perms,
			}
		end,
		exit_block = function(self, term, shadowed)
			-- -> env, term
			shadowed = shadowed.shadowed or error "shadowed.shadowed missing"
			local env = new_env {
				locals = shadowed.locals,
				nonlocals = shadowed.nonlocals,
				perms = shadowed.perms,
			}
			local wrapped = term
			for idx = self.bindings:len(), 1, -1 do
				local binding = self.bindings:get(idx)
				if not binding then
					error "missing binding"
				end
				if binding:is_let() then
					local name, expr = binding:unwrap_let()
					wrapped = terms.inferrable_term.let(name, expr, wrapped)
				elseif binding:is_tuple_elim() then
					local names, subject = binding:unwrap_tuple_elim()
					wrapped = terms.inferrable_term.tuple_elim(subject, wrapped)
				end
			end

			return env, wrapped
		end,
	},
}

local function dump_env(env)
	return "Environment" .. "\nlocals: " .. trie.dump_map(env.locals) .. "\nnonlocals: " .. trie.dump_map(env.nonlocals)
end

return {
	new_env = new_env,
	dump_env = dump_env,
}
