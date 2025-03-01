require "lua-init"
local luaunit = require "luaunit"
local format = require "format"

local function simplify_list(list, remove_comments)
	if not list then
		return nil
	end
	if list.kind == "list" then
		local simplified_list = {}

		for i = 1, #list.elements do
			local result = simplify_list(list.elements[i], remove_comments)
			table.insert(simplified_list, result)
		end

		return simplified_list
	else
		if list.kind == "literal" then
			return list.val
		elseif list.kind == "symbol" then
			return list.str
		elseif list.kind == "comment" then
			if not remove_comments then
				return list.val
			end
			return nil
		elseif list.kind == "string" then
			local val = ""

			for _, v in ipairs(list.elements) do
				for _, c in ipairs(v.val) do
					val = val .. string.char(c)
				end
			end

			return { kind = "string", elements = { val } }
		else
			print("error, unsupported value: ", list.kind)
		end
	end
end

local function create_anchor(internal, id, line, char)
	if id == nil then
		id = "inline"
	end
	return format.create_anchor(internal, id, line, char)
end

local function create_list(start_anchor, end_anchor, elements)
	return {
		start_anchor = start_anchor,
		end_anchor = end_anchor,
		kind = "list",
		elements = elements,
	}
end

local function create_symbol(start_anchor, symbol)
	return {
		start_anchor = start_anchor,
		kind = "symbol",
		str = symbol,
	}
end

-- assert that the cursor is always moving forward
local function forward_moving_cursor(element, cursor)
	local cursor = cursor -- the moving cursor

	if element.kind == "list" then
		if not cursor then
			cursor = element.start_anchor
		else
			if not (element.start_anchor >= cursor) then
				-- print("failed, ", element.start_anchor, " >= ", cursor)
				return false
			end
		end

		for i, v in ipairs(element.elements) do
			local accumulator, newcursor = forward_moving_cursor(element.elements[i], cursor)

			if not accumulator then
				-- print("accumulator failure")
				return false
			end
			if not (newcursor >= cursor) then
				-- print("failed, ", newcursor, " >= ", cursor)
				return false
			end

			cursor = newcursor
		end

		if not (element.end_anchor >= cursor) then
			-- print("failed, ", element.end_anchor, " >= ", cursor)
			return false
		end
		cursor = element.end_anchor

		return true, cursor
	elseif element.kind == "literal" or element.kind == "symbol" or element.kind == "comment" then
		-- print(element.start_anchor, " >= ", cursor, ", ", element.start_anchor >= cursor)
		return element.start_anchor >= cursor, element.start_anchor
	end

	return true, cursor
end

local function samelength_testfile_list(text, ast)
	local _, num_newlines = text:gsub("\n", "\n")

	if not ((ast.end_anchor.line == num_newlines) or (ast.end_anchor.line == (num_newlines + 1))) then
		print("ast: ", ast.end_anchor.line, "num_newlines:", num_newlines)
	end
	-- print(inspect(ast))

	-- why is this even necessary??
	return (ast.end_anchor.line == num_newlines) or (ast.end_anchor.line == (num_newlines + 1))
end

local function compare_list_anchors(actual, expected)
	if
		(
			expected.start_anchor.line == actual.start_anchor.line
			and expected.start_anchor.char == actual.start_anchor.char
		) and (expected.kind == actual.kind)
	then
		if expected.kind == "list" then
			if
				not (
					expected.end_anchor.line == actual.end_anchor.line
					and expected.end_anchor.char == actual.end_anchor.char
				)
			then
				print(
					"expected end_anchor: ",
					expected.end_anchor,
					expected.kind,
					" actual: ",
					actual.end_anchor,
					actual.kind
				)
				return false
			end

			for i, _ in ipairs(expected.elements) do
				if not compare_list_anchors(actual.elements[i], expected.elements[i]) then
					return false
				end
			end
		end
		return true
	else
		print(
			"expected start_anchor: ",
			expected.start_anchor,
			expected.kind,
			" actual: ",
			actual.start_anchor,
			actual.kind
		)
		return false
	end
end

function testOldOpensCase()
	local example = [[
do
	let m =
		module
			let y = 3
			let add =
				basic-fn (a b)
					+ a b
	let x = 5
	use-mod m
	dump-env;
	add x y
]]

	local expected = {
		{
			"do",
			{
				"let",
				"m",
				"=",
				{
					"module",
					{ "let", "y", "=", 3 },
					{ "let", "add", "=", { "basic-fn", { "a", "b" }, { "+", "a", "b" } } },
				},
			},
			{ "let", "x", "=", 5 },
			{ "use-mod", "m" },
			{ "dump-env" },
			{ "add", "x", "y" },
		},
	}

	local parsed = format.parse(example, "inline")
	local simplified = simplify_list(parsed)

	luaunit.assertEquals(simplified, expected)
end

function testOpensCase()
	local example = [[
let m =
	module
		let y = 3
		let add =
			basic-fn (a b)
				+ a b
let x = 5
use-mod m
dump-env;
add x y
]]

	local expected = {
		{
			"let",
			"m",
			"=",
			{
				"module",
				{ "let", "y", "=", 3 },
				{ "let", "add", "=", { "basic-fn", { "a", "b" }, { "+", "a", "b" } } },
			},
		},
		{ "let", "x", "=", 5 },
		{ "use-mod", "m" },
		{ "dump-env" },
		{ "add", "x", "y" },
	}

	local parsed = format.parse(example, "inline")
	local simplified = simplify_list(parsed)

	luaunit.assertEquals(simplified, expected)
end

function testsinglelist()
	local example = {
		[[
lambda
	;
		x : i32
		y : i32
		z : some_complicated_type(x, y)
	body body body
	body body
	result
]],
		[[
f a
	g b
	g c
		g d
]],
		[[
f a;
	g b
	g c;
		g d
]],
		[[
f a; w
	g b
	g c;
		g d
]],
		[[
f a; w;
	g b
	g c;
		g d
]],
		[[

dump-env
number2

anotherthing

something else
	hello friend
		hi again
]],
		[[
;
	1 x
	2 y
	3 z
]],
		[[
;
	(1 x)
	(2 y)
	(3 z)
]],
		[[
a b c
	d e f
		g h i
	j k l
]],
		[[
print a; print b;
	print c; print d;
]],
	}

	local expected = {
		{
			{
				"lambda",
				{ { "x", ":", "i32" }, { "y", ":", "i32" }, { "z", ":", { "some_complicated_type", "x", "y" } } },
				{ "body", "body", "body" },
				{ "body", "body" },
				"result",
			},
		},

		{ { "f", "a", { "g", "b" }, { "g", "c", { "g", "d" } } } },
		{ { { "f", "a" }, { "g", "b" }, { { "g", "c" }, { "g", "d" } } } },
		{ { { "f", "a" }, "w", { "g", "b" }, { { "g", "c" }, { "g", "d" } } } },
		{ { { "f", "a" }, { "w" }, { "g", "b" }, { { "g", "c" }, { "g", "d" } } } },

		{
			"dump-env",
			"number2",
			"anotherthing",
			{ "something", "else", { "hello", "friend", { "hi", "again" } } },
		},
		{ { { 1, "x" }, { 2, "y" }, { 3, "z" } } },
		{ { { 1, "x" }, { 2, "y" }, { 3, "z" } } },
		{ { "a", "b", "c", { "d", "e", "f", { "g", "h", "i" } }, { "j", "k", "l" } } },
		{
			{ { "print", "a" }, { "print", "b" }, { { "print", "c" }, { "print", "d" } } },
		},
	}

	for i = 1, #example do
		local results = format.parse(example[i], ("inline example " .. tostring(i) .. " "))
		luaunit.assertTrue(forward_moving_cursor(results))
		luaunit.assertTrue(samelength_testfile_list(example[i], results))
		luaunit.assertEquals(simplify_list(results), expected[i])
	end
end

function testSymbols()
	local example = {
		"some_identifier",
		"_some_identifier",
		"some-identifier",
		"SomeIdentifier",
		"&+",
		">~",
		">>=",
		"and=",
		"str+str",
		"_42",
		"=303",
		"-[_]/[_]->",
		"[_][_]{_}",
		"_[_]",
	}

	local expected = {
		{ "some_identifier" },
		{ "_some_identifier" },
		{ "some-identifier" },
		{ "SomeIdentifier" },
		{ "&+" },
		{ ">~" },
		{ ">>=" },
		{ "and=" },
		{ "str+str" },
		{ "_42" },
		{ "=303" },
		{ "-[_]/[_]->" },
		{ "[_][_]{_}" },
		{ "_[_]" },
	}

	for i = 1, #example do
		local results = format.parse(example[i], ("inline example " .. tostring(i) .. " "))
		luaunit.assertTrue(forward_moving_cursor(results))
		luaunit.assertTrue(samelength_testfile_list(example[i], results))
		luaunit.assertEquals(simplify_list(results), expected[i])
	end
end

function testNumbers()
	local example = {
		"0",
		"23",
		"42",
		"-303",
		"12",
		"-1",
		"-32",
		"45054",
		"0",
		"1",
		"3.14159",
		"-2",
		"3e-06",
		"41984.640625",
		"1.234e+24",
		"-1e-12",
		"1.0:f64",
		"0:u64",
		"0:i8",
	}

	local expected = {
		{ 0 },
		{ 23 },
		{ 42 },
		{ -303 },
		{ 12 },
		{ -1 },
		{ -32 },
		{ 45054 },
		{ 0 },
		{ 1 },
		{ 3.14159 },
		{ -2 },
		{ 3e-06 },
		{ 41984.640625 },
		{ 1.234e+24 },
		{ -1e-12 },
		{ 1.0 },
		{ 0 },
		{ 0 },
	}

	for i = 1, #example do
		local results = format.parse(example[i], "inline")
		luaunit.assertTrue(forward_moving_cursor(results))
		luaunit.assertEquals(simplify_list(results), expected[i])
		luaunit.assertTrue(samelength_testfile_list(example[i], results))
	end
end

function testnakedlist()
	local example = {
		[[
print
	+ 1 2
		3 * 4
]],
		[[
print
	+ 1 2 (3 * 4)
]],
		[[
print
	42
]],
		[[
print
	# hello
	42
]],
		[[
print
	42 #testing
	#### hello

]],
		[[
print
	(+ 1 2
		\ 3 * 4)
]],
		"foo\n\t\n\tbar",
		[[
foo

bar
]],

		"foo baz intnop\n\t\nbar",
		"foo\n\t\nbar",
	}

	local expected = {
		{ { "print", { "+", 1, 2, { 3, "*", 4 } } } },
		{ { "print", { "+", 1, 2, { 3, "*", 4 } } } },
		{ { "print", 42 } },
		{ { "print", 42 } },
		{ { "print", 42 } },
		{ { "print", { "+", 1, 2, { 3, "*", 4 } } } },
		{ { "foo", "bar" } },
		{ "foo", "bar" },
		{ { "foo", "baz", "intnop" }, "bar" },
		{ "foo", "bar" },
	}

	for i = 1, #example do
		local results = format.parse(example[i], ("inline example " .. tostring(i) .. " "))
		luaunit.assertEquals(simplify_list(results, true), expected[i])
		luaunit.assertTrue(forward_moving_cursor(results))
		luaunit.assertTrue(samelength_testfile_list(example[i], results))
	end
end

function testempty()
	local example = [[

    ]]

	local expected = {}

	local parsed = format.parse(example, "inline")
	luaunit.assertEquals(simplify_list(parsed), expected)
	luaunit.assertTrue(samelength_testfile_list(example, parsed))
end

function testnakedlist2()
	local example = {
		"hello hi greetings",
		[[
toplevel
	nested hi
		innerlayer
	outerlayer]],
		[[toplevel
	innerlevel
		innestlevel]],
	}

	local expected = {
		{ { "hello", "hi", "greetings" } },
		{ { "toplevel", { "nested", "hi", "innerlayer" }, "outerlayer" } },
		{ { "toplevel", { "innerlevel", "innestlevel" } } },
	}

	for i = 1, #example do
		local results = format.parse(example[i], ("inline example " .. tostring(i) .. " "))
		local parsed = simplify_list(results)
		luaunit.assertEquals(parsed, expected[i])
		luaunit.assertTrue(samelength_testfile_list(example[i], results))
	end
end

function testbracedlist()
	local example = {
		"(hello hi greetings)",
		"(hello (hi (another)) greetings)",
		"(hello; (greetings;); anothertest)",
		"(hello\n\tfailure \n\n\t\t\t\n\t\t(hi (another)) greetings)",
		"a[b][c](d)",
		"a -[b]/[c]-> d",
	}

	local expected = {
		{ { "hello", "hi", "greetings" } },
		{ { "hello", { "hi", { "another" } }, "greetings" } },
		{ { { "hello" }, { { { "greetings" } } }, "anothertest" } },
		{ { "hello", "failure", { "hi", { "another" } }, "greetings" } },
		{ { { "_[_]", { "_[_]", "a", "b" }, "c" }, "d" } },
		{ { "a", { "-[_]/[_]->", { "b" }, { "c" } }, "d" } },
	}

	for i = 1, #example do
		local results = format.parse(example[i], ("inline example " .. tostring(i) .. " "))
		luaunit.assertTrue(forward_moving_cursor(results))
		luaunit.assertEquals(simplify_list(results), expected[i])
		luaunit.assertTrue(samelength_testfile_list(example[i], results))
	end
end

function testcomments()
	local example = {
		"1\n# list of one\n1",
		"#### i am a normal comment created by a normal human\n\tand this comment is intended to be useful\n\t\tsee?\n\n\tall of this is on one line ",
		"# i",

		"# comment A\ntoken",
		"#### comment B\n\ttoken",
		"token\n#### comment C\n\ttoken",
		"token\n\ttoken\n\t# comment D\n\ttoken",
		"#### comment G\n\t\ttoken",
		"#### comment H\n\t\t\ttoken",
		"#### comment I\n\ttoken\n\ttoken",
		"#### comment J\n\t\ttoken\n\ttoken",
		"#### comment K\n\t\ttoken\n\t\ttoken",
		"#### comment L\n\ttoken\n\t\ttoken",
		"token\n\t# comment M\n\ttoken\n\t\ttoken",
		"token\n\t# comment N\n\ttoken\ntoken",
		"token\n\t#### comment O\n\t\ttoken\ntoken",
		"token\n\t#### comment P\n\t\ttoken\n\ttoken",
		"token\n\t#### comment Q\n\t\ttoken\n\t\ttoken",
		"token\n\t#### comment R\n\t\ttoken\n\t\t\ttoken",
		"token # comment S1\ntoken",
		"token # comment S2\n\ttoken",
		"token # comment S3\n\ttoken\n\ttoken",
		"token # comment S4\n\ttoken\n\t\ttoken",
		"token # comment T# comment # comment",
		'#### comment U\n\t""""',

		[[
let (orig-results) = get-prim-func-res-inner(wrap(type, foo), prim-nil)
let orig-results = unwrap(func-conv-res-type(oldargs), orig-results)
let new-results =
	lambda ((args : unwrap(type, newargs)))
		# comment
		let ptuple = tuple-to-prim-tuple(oldargs, oldargs-valid, args)
		let orig-results-res = apply(orig-results, ptuple)
		let (newres valid) = orig-results-res
		newres
]],
	}

	local expected = {
		{ 1, " list of one", 1 },
		{
			" i am a normal comment created by a normal human\nand this comment is intended to be useful\n\tsee?\n\nall of this is on one line ",
		},
		{ " i" },
		{ " comment A", "token" },
		{ " comment B\ntoken" },
		{ "token", " comment C\ntoken" },
		{ { "token", "token", " comment D", "token" } },
		{ " comment G\n\ttoken" },
		{ " comment H\n\t\ttoken" },
		{ " comment I\ntoken\ntoken" },
		{ " comment J\n\ttoken\ntoken" },
		{ " comment K\n\ttoken\n\ttoken" },
		{ " comment L\ntoken\n\ttoken" },
		{ { "token", " comment M", { "token", "token" } } },
		{ { "token", " comment N", "token" }, "token" },
		{ "token", " comment O\ntoken", "token" },
		{ { "token", " comment P\ntoken", "token" } },
		{ "token", " comment Q\ntoken\ntoken" },
		{ "token", " comment R\ntoken\n\ttoken" },
		{ "token", " comment S1", "token" },
		{ { "token", " comment S2", "token" } },
		{ { "token", " comment S3", "token", "token" } },
		{ { "token", " comment S4", { "token", "token" } } },
		{ "token", " comment T# comment # comment" },
		{ ' comment U\n""""' },
		{
			{ "let", { "orig-results" }, "=", { "get-prim-func-res-inner", { "wrap", "type", "foo" }, "prim-nil" } },
			{ "let", "orig-results", "=", { "unwrap", { "func-conv-res-type", "oldargs" }, "orig-results" } },
			{
				"let",
				"new-results",
				"=",
				{
					"lambda",
					{ { "args", ":", { "unwrap", "type", "newargs" } } },
					" comment",
					{ "let", "ptuple", "=", { "tuple-to-prim-tuple", "oldargs", "oldargs-valid", "args" } },
					{ "let", "orig-results-res", "=", { "apply", "orig-results", "ptuple" } },
					{ "let", { "newres", "valid" }, "=", "orig-results-res" },
					"newres",
				},
			},
		},
	}

	for i = 1, #example do
		local results = format.parse(example[i], ("inline example " .. tostring(i) .. " "))
		luaunit.assertTrue(samelength_testfile_list(example[i], results))
		luaunit.assertEquals(simplify_list(results, false), expected[i])
	end
end

function testfailedparse()
	local example = {
		"\ttoken\ntoken",
		"\ttoken # comment\ntoken",
		'\t""""',

		"\t# comment E1\n\ttoken",
		"\t# comment F1\n\t\ttoken",
		"\t# comment C1\ntoken",
		"\t#comment",
		"# comment\n    token",
		"token\n    #comment",
		"    token\n    #comment",
		"    # comment\n    #comment",
		"token\n    \ttoken",
		"token\n\t    token",
		"token\n        token",
		"token\n    #comment",
		" #",
		" A",
	}
	for i = 1, #example do
		local function assertFunction()
			local results = format.parse(example[i], ("inline example " .. tostring(i) .. " "))
		end

		local success, errorMessage = pcall(assertFunction)

		if not success then
			-- pass
		else
			luaunit.fail("Test testwrongcomments 'succeeded' when it should have failed:\n" .. example[i] .. "\n")
		end
	end
end

function testcomma()
	local example = {
		"f(a, b, c)",
		"f (a)",
		"f(x y)",
		"a f(a)",
		"a f(x(x) - y)",
		"f(x(x) - y)",
		"f(x - y)",
		"f((x + 3) + 2 * d)",
		"f(x + y)",
		"{ a = 1, b = 2 }",
		"{c = a, b = d, e = 1 + 2 * (3 + 6)}",
		"def f (a : int, b : int) (a + b)",
		"f((a, b),c)",
		"[1 , 2, 1 + 2]",
		"let (a, b) = f(x)",
		"f(a)",
		"f()",
		"f()()",
		"f(x, y)(x)",
		"f(x + 1, y)(x)(z)",
		[[
let(
	letn't,
	=,
	let)
		]],
		"a x(y(z) - b) - c",
		"x(y(z) - b(d))(x) - c",
		"let d1 = abs(length(uv) - r) - t",
	}

	local expected = {
		{ { "f", "a", "b", "c" } },
		{ { "f", { "a" } } },
		{ { "f", { "x", "y" } } },
		{ { "a", { "f", "a" } } },
		{ { "a", { "f", { { "x", "x" }, "-", "y" } } } },
		{ { "f", { { "x", "x" }, "-", "y" } } },
		{ { "f", { "x", "-", "y" } } },
		{ { "f", { { "x", "+", 3 }, "+", 2, "*", "d" } } },
		{ { "f", { "x", "+", "y" } } },
		{ { "curly-list", { "a", "=", 1 }, { "b", "=", 2 } } },
		{ { "curly-list", { "c", "=", "a" }, { "b", "=", "d" }, { "e", "=", 1, "+", 2, "*", { 3, "+", 6 } } } },
		{ { "def", "f", { { "a", ":", "int" }, { "b", ":", "int" } }, { "a", "+", "b" } } },
		{ { "f", { "a", "b" }, "c" } },
		{ { "square-list", 1, 2, { 1, "+", 2 } } },
		{ { "let", { "a", "b" }, "=", { "f", "x" } } },
		{ { "f", "a" } },
		{ { "f" } },
		{ { { "f" } } },
		{ { { "f", "x", "y" }, "x" } },
		{ { { { "f", { "x", "+", 1 }, "y" }, "x" }, "z" } },
		{ { "let", "letn't", "=", "let" } },
		{ { "a", { "x", { { "y", "z" }, "-", "b" } }, "-", "c" } },
		{ { { { "x", { { "y", "z" }, "-", { "b", "d" } } }, "x" }, "-", "c" } },
		{ { "let", "d1", "=", { "abs", { { "length", "uv" }, "-", "r" } }, "-", "t" } },
	}

	for i = 1, #example do
		local results = format.parse(example[i], ("inline example " .. tostring(i) .. " "))
		-- print(inspect(results))
		luaunit.assertEquals(simplify_list(results), expected[i])
		luaunit.assertTrue(samelength_testfile_list(example[i], results))
	end
end

function testanchors()
	local example = {
		"hello hi greetings",
		[[
hello
	nested
hi
]],
		[[
hello
	nested a
hi
]],

		[[
hello
(this is
	a test)
]],
		[[
hello
	(this is
		a test)
]],
		-- 		[[
		-- toplevel
		-- 	nested hi
		-- 		innerlayer
		-- 	outerlayer]],
		-- 		[[toplevel
		-- 	innerlevel
		-- 		innestlevel]],
	}

	local expected = {
		create_list(create_anchor(false, nil, 1, 1), create_anchor(false, nil, 1, 19), {
			create_list(create_anchor(false, nil, 1, 1), create_anchor(false, nil, 1, 19), {
				create_symbol(create_anchor(false, nil, 1, 1), "hello"),
				create_symbol(create_anchor(false, nil, 1, 7), "hi"),
				create_symbol(create_anchor(false, nil, 1, 10), "greetings"),
			}),
		}),

		create_list(create_anchor(false, nil, 1, 1), create_anchor(false, nil, 4, 1), {
			create_list(create_anchor(false, nil, 1, 1), create_anchor(false, nil, 2, 8), {
				create_symbol(create_anchor(false, nil, 1, 1), "hello"),
				create_symbol(create_anchor(false, nil, 2, 2), "nested"),
			}),
			create_symbol(create_anchor(false, nil, 3, 1), "hi"),
		}),

		create_list(create_anchor(false, nil, 1, 1), create_anchor(false, nil, 4, 1), {
			create_list(create_anchor(false, nil, 1, 1), create_anchor(false, nil, 2, 10), {
				create_symbol(create_anchor(false, nil, 1, 1), "hello"),
				create_list(create_anchor(false, nil, 2, 2), create_anchor(false, nil, 2, 10), {
					create_symbol(create_anchor(false, nil, 2, 2), "nested"),
					create_symbol(create_anchor(false, nil, 2, 9), "a"),
				}),
			}),
			create_symbol(create_anchor(false, nil, 3, 1), "hi"),
		}),

		create_list(create_anchor(false, nil, 1, 1), create_anchor(false, nil, 4, 1), {
			create_symbol(create_anchor(false, nil, 1, 1), "hello"),
			create_list(create_anchor(false, nil, 2, 1), create_anchor(false, nil, 3, 9), {
				create_symbol(create_anchor(false, nil, 2, 2), "this"),
				create_symbol(create_anchor(false, nil, 2, 7), "is"),
				create_symbol(create_anchor(false, nil, 3, 2), "a"),
				create_symbol(create_anchor(false, nil, 3, 4), "test"),
			}),
		}),
		create_list(create_anchor(false, nil, 1, 1), create_anchor(false, nil, 4, 1), {
			create_list(create_anchor(false, nil, 1, 1), create_anchor(false, nil, 4, 1), {
				create_symbol(create_anchor(false, nil, 1, 1), "hello"),
				create_list(create_anchor(false, nil, 2, 2), create_anchor(false, nil, 3, 10), {
					create_symbol(create_anchor(false, nil, 2, 3), "this"),
					create_symbol(create_anchor(false, nil, 2, 8), "is"),
					create_symbol(create_anchor(false, nil, 3, 3), "a"),
					create_symbol(create_anchor(false, nil, 3, 5), "test"),
				}),
			}),
		}),
	}

	assert(#expected == #example)

	for i = 1, #example do
		local results = format.parse(example[i], ("inline example " .. tostring(i) .. " "))
		luaunit.assertEquals(simplify_list(results), simplify_list(expected[i]))
		luaunit.assertTrue(compare_list_anchors(results, expected[i]))
		luaunit.assertTrue(forward_moving_cursor(results))
		luaunit.assertTrue(samelength_testfile_list(example[i], results))
	end
end

function testlongstring()
	local example = {
		[[
let array-type =
	intrinsic
		""""
			local terms = require './terms'
			local value = terms.value
			local gens = require './terms-generators'
			local value_array = gens.declare_array(value)
			local id = {name = "array"}
			local function mktype(elem)
				return value.prim_boxed_type(id, value_array(elem))
			end
			return mktype
		prim-func-type (T : prim-type) -> (array : prim-type)

]],
		-- goal: ensure indenting rules are followed
		'""""\n\ttoken',
		'""""something\n\tblahblahblah', -- may or may not be legal
		'""""\n\t# comment',
		'token\n""""\n\ttoken',
		'token\n\t""""\n\ttoken',
		'token\n\t""""\n\t\ttoken',
		'token\n\t""""\ntoken',
		'token\n\t""""\n\t\ttoken\ntoken',
	}

	local expected = {
		{
			{
				"let",
				"array-type",
				"=",
				{
					"intrinsic",
					{
						kind = "string",
						elements = {
							"\n" .. [[
local terms = require './terms'
local value = terms.value
local gens = require './terms-generators'
local value_array = gens.declare_array(value)
local id = {name = "array"}
local function mktype(elem)
	return value.prim_boxed_type(id, value_array(elem))
end
return mktype]],
						},
					},
					{ "prim-func-type", { "T", ":", "prim-type" }, "->", { "array", ":", "prim-type" } },
				},
			},
		},
		{ { elements = { "\ntoken" }, kind = "string" } },
		{ { elements = { "something\nblahblahblah" }, kind = "string" } },
		{ { elements = { "\n# comment" }, kind = "string" } },
		{ "token", { elements = { "\ntoken" }, kind = "string" } },
		{ { "token", { elements = { "" }, kind = "string" }, "token" } },
		{ { "token", { elements = { "\ntoken" }, kind = "string" } } },
		{ { "token", { elements = { "" }, kind = "string" } }, "token" },
		{ { "token", { elements = { "\ntoken" }, kind = "string" } }, "token" },
	}

	assert(#expected == #example)

	for i = 1, #example do
		local results = format.parse(example[i], ("inline example " .. tostring(i) .. " "))
		-- print("test# ", i)
		-- print("results: ", inspect(results))
		luaunit.assertEquals(simplify_list(results), expected[i])
		luaunit.assertTrue(forward_moving_cursor(results))
		luaunit.assertTrue(samelength_testfile_list(example[i], results))
	end
end

function test_unformatter()
	local filename = "prelude.alc"
	local unformat = require "./unformatter"

	local f = io.open(filename, "r")
	if not f then
		luaunit.fail(filename .. " does not exist")
	end
	f:close()

	local src = ""
	for line in io.lines(filename) do
		src = src .. "\n" .. line
	end

	local function compare_lists(a, b)
		assert(a.kind == "list")
		assert(b.kind == "list")

		for i = 1, #a.elements do
			if not (a.elements[i].kind == b.elements[i].kind) then
				print(a.elements[i].kind, b.elements[i].kind, i)
				return false
			end
			if a.elements[i].kind == "list" then
				if not compare_lists(a.elements[i], b.elements[i]) then
					return false
				end
			end
		end

		return true
	end

	local formatted = format.parse(src, filename)

	local unformatted = unformat.unformat(formatted)

	local format_verify = format.parse(unformatted, filename)

	luaunit.assertTrue(compare_lists(formatted, format_verify))
end

os.exit(luaunit.LuaUnit.run())
