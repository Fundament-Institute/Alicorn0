;; SPDX-License-Identifier: Apache-2.0
;; SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

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
		"substitute_inner" ; 4
		"substitute_inner_impl" ; 4
		"slice_constraints_for" ; 4
	)
	arguments: (arguments
		. (_) . (_) . (_) . ; 3
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
		"substitute_inner" ; 4
		"substitute_inner_impl" ; 4
		"slice_constraints_for" ; 4
	)
	arguments: (arguments
		. (_) . (_) . (_) . (_) . (_) . ; 5
	)
) @function.call
