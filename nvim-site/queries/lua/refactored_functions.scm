;; Write queries here (see $VIMRUNTIME/queries/ for examples).
;; Move cursor to a capture ("@foo") to highlight matches in the source buffer.
;; Completion for grammar nodes is available (:help compl-omni)

(function_call
	name: [
		(identifier) @_function.name
		(dot_index_expression
			table: (_)
			field: (identifier) @_function.name
		)
		(method_index_expression
			table: (_)
			method: (identifier) @_function.name
		)
	]
	(#any-eq? @_function.name
		"apply_value"
		"infer_tuple_type"
		"infer_tuple_type_unwrapped"
	)
	arguments: (arguments
		. (_) . (_) .
	)
) @function.call

(function_call
	name: [
		(identifier) @_function.name
		(dot_index_expression
			table: (_)
			field: (identifier) @_function.name
		)
		(method_index_expression
			table: (_)
			method: (identifier) @_function.name
		)
	]
	(#any-eq? @_function.name
		"extract_desc_nth"
		"make_inner_context"
	)
	arguments: (arguments
		. (_) . (_) . (_) .
	)
) @function.call
