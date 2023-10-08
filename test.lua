local luaunit = require 'luaunit'
local format = require 'format'
local inspect = require 'inspect'

local function simplify_list(list)

	if list.kind == "list" then
		local simplified_list = {}

		for i = 1, #list.elements do
			table.insert(simplified_list, simplify_list(list.elements[i]))
		end

		return simplified_list
	else
		if list.kind == "literal" then
			return list.val
		elseif list.kind == "symbol" then
			return list.str
		elseif list.kind == "comment" then
			return list.val
		else
			print("error, unsupported value: ", list.kind)
		end
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

    local expected = {{ "do",
    {"let", "m", "=",
    {"module",
        {"let", "y", "=", 3},
        {"let", "add", "=",
        {"basic-fn", {"a", "b"}, {"+", "a", "b"}}
    }}},
    {"let", "x", "=", 5},
    {"use-mod", "m"},
    {"dump-env"},
    {"add", "x", "y"}
    }}

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
    {"let", "m", "=",
    {"module",
        {"let", "y", "=", 3},
        {"let", "add", "=",
        {"basic-fn", {"a", "b"}, {"+", "a", "b"}}
    }}},
    {"let", "x", "=", 5},
    {"use-mod", "m"},
    {"dump-env"},
    {"add", "x", "y"}
    }

    local parsed = format.parse(example, "inline")
    local simplified = simplify_list(parsed)

    luaunit.assertEquals(simplified, expected)

end

function testsinglelist()
    local example = {
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
    print a; print b
    ;
        print c; print d
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
]]
	}

    local expected = {
	{
	  "dump-env", "number2", "anotherthing", {"something", "else", {"hello", "friend", {"hi", "again"}}}
	},
	{{{}, {1, "x"}, {2, "y"}, {3, "z"}
	}},
	{
		{}, { "print", "a" }, { "print", "b" }, {}, { { "print", "c" }, { "print", "d" } }
	},
	{{}, {1, "x"}, {2, "y"}, {3, "z"}},
	{{"a", "b", "c", {"d", "e", "f", {"g", "h", "i"}}, {"j", "k", "l"}}}
	}


    for i = 1,#example do
      local results = format.parse(example[i], "inline")
      luaunit.assertEquals(simplify_list(results), expected[i])
    end
end



function testSymbols()
    local example = {
      "some_identifier", "_some_identifier",
      "some-identifier",
      "SomeIdentifier",
      "&+", ">~", ">>=", "and=", "str+str",
      "_42", "=303"
    }

    local expected = {
        {"some_identifier"},
        {"_some_identifier"},
        {"some-identifier"},
        {"SomeIdentifier"},
        {"&+"},
        {">~"},
        {">>="},
        {"and="},
        {"str+str"},
        {"_42"},
        {"=303"}
    }

    for i = 1,#example do
      local results = format.parse(example[i], "inline")
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
        {0},
        {23},
        {42},
        {-303},
        {12},
        {-1},
        {-32},
        {45054},
        {0},
        {1},
        {3.14159},
        {-2},
        {3e-06},
        {41984.640625},
        {1.234e+24},
        {-1e-12},
        {1.0},
        {0},
        {0},
    }

    for i = 1,#example do
        local results = format.parse(example[i], "inline")
        luaunit.assertEquals(simplify_list(results), expected[i])
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
-- TODO: Fix this
-- [[
-- print
-- 	(+ 1 2
-- 		\ 3 * 4)
-- ]]
}

	local expected = {
		{{ "print", {"+", 1, 2, {3, "*", 4}} }},
		{{ "print", {"+", 1, 2, {3, "*", 4}} }},
		{{ "print", 42 }},
	}


    for i = 1,#example do
        local results = format.parse(example[i], "inline")
        luaunit.assertEquals(simplify_list(results), expected[i])
    end
end

function testempty()
    local example = [[



    ]]

	local expected = {}

	local parsed = format.parse(example, "inline")
	luaunit.assertEquals(simplify_list(parsed), expected)

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
		innestlevel]]
	}

	local expected = {
		{{ "hello", "hi", "greetings" }},
		{{ "toplevel", { "nested", "hi", "innerlayer" }, "outerlayer" }},
		{{ "toplevel", {"innerlevel", "innestlevel"} }}
	}

    for i = 1,#example do
        local results = format.parse(example[i], "inline")
		local parsed = simplify_list(results)
        luaunit.assertEquals(parsed, expected[i])
    end


end

function testbracedlist()
    local example = {
		"(hello hi greetings)",
		"(hello (hi (another)) greetings)",
		"(hello; (greetings;); anothertest)",
		"(hello\n failure \n\n\t\t \t\n(hi (another)) greetings)",
	}

	local expected = {
		{{"hello", "hi", "greetings"}},
		{{"hello", {"hi", { "another"}}, "greetings"}},
		{{{"hello"}, {{{"greetings"}}}, "anothertest"}},
		{{"hello", "failure", {"hi", { "another"}}, "greetings"}},
	}

    for i = 1,#example do
        local results = format.parse(example[i], "inline")
        luaunit.assertEquals(simplify_list(results), expected[i])
    end


end

function testcomments()
	local example = {
		"1\n# list of one\n1",
		"# i am a normal comment created by a normal human\n\tand this comment is intended to be useful\n\t\tsee?\n\n\tall of this is on one line ",
		"# i",
-- [[
-- # aaaaa
-- 	Ma'am is acceptable in a crunch, but I prefer Captain.
-- 		          	-- Kathryn Janeway
-- ]]
	}

	local expected = {
		{1, " list of one", 1},
		{" i am a normal comment created by a normal human\n\tand this comment is intended to be useful\n\t\tsee?\n\n\tall of this is on one line "},
		{" i"},
	}

    for i = 1,#example do
        local results = format.parse(example[i], "inline")
        luaunit.assertEquals(simplify_list(results), expected[i])
    end
end

os.exit( luaunit.LuaUnit.run() )
