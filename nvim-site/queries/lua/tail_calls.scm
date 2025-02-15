;; Write queries here (see $VIMRUNTIME/queries/ for examples).
;; Move cursor to a capture ("@foo") to highlight matches in the source buffer.
;; Completion for grammar nodes is available (:help compl-omni)

(return_statement
	(expression_list
		[
			(function_call
				name: [
					(identifier) @_function_name
					(dot_index_expression
						field: (identifier) @_function_name
					)
					(method_index_expression
						method: (identifier) @_function_name
					)
				]
				(#not-any-of? @_function_name
					"getmetatable"
					"notail"
					"pack"
					"setmetatable"
					"tostring"
					"unpack"
					"var_debug"
				)
			)
			(function_call
				name: (parenthesized_expression)
			)
		]
	)
) @tail_call
