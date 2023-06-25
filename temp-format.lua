-- local inspect = require('inspect')
local lpeg = require("lpeg")
local P, S, C, Ct, Cg, Cp, R, V = lpeg.P, lpeg.S, lpeg.C, lpeg.Ct, lpeg.Cg, lpeg.Cp, lpeg.R, lpeg.V

local grammar = {}

lpeg.locale(lpeg)

wsp_chars = S"\n\t\r "
wsp = wsp_chars^0


function enum(tbl)
    for i = 1,#tbl do
        local v = tbl[i]
        tbl[v] = tbl[i]
    end

    return tbl
end

local token_raw = enum {
    "comment_begin",
    "blockstring",
    "string_char",
    "list_start",
    "list_end",
    "list_sep",
    "splice_control",
    "newline"
}


-- SLN
-- expressions, atoms, lists

-- if I just immediately transform numbers into lua numbers, bignum constants will suffer.
-- this probably isn't a problem, and scopes shares this problem
function handle_numbers(pos_start, val, type)
    if type ~= nil then
        return { anchor = { char = pos_start }, kind = "literal", literaltype = type, val = tonumber(val) }
    end

    -- what hole does this number go in?
    -- that's right! the double hole!
    if type == nil then
        return { anchor = { char = pos_start }, kind = "literal",  literaltype = "f64", val = tonumber(val) }
    end
end

grammar.number = P{
    "number",
    number = Cg(((Cp() * C(V"float_special" + V"hex" + V"big_e") * V"types"^0)) / handle_numbers);
    types = (P":" * C((S"iu" * (P"8" + P"16" + P"32" + P"64")) + (P"f" * (P"32" + P"64")))),
    digit = R("09")^1;
    hex_digit = (V"digit" + R"AF" + R"af")^1;
    decimal = S"-+"^0 * V"digit" * (P"." * V"digit")^0;
    hex = S"+-"^0 * P"0x" *  V"hex_digit" * (P"." * V"hex_digit")^0;
    big_e = V"decimal" * (P"e" * V"decimal")^0;
    float_special = P"+inf" + P"-inf" + P"nan";
}

function get_grammar_position(grammar, tokenrename)
    function turn_to_thing(char, pos)
        return { anchor = { char = pos, line = 0 }, kind = tokenrename };
    end

    return C(Cp() * grammar) / turn_to_thing
end

function handle_newlines(tabsplusnewline, pos, tabs)

    local numtabs = 0
    for i in string.gmatch(tabs, "\t") do
        numtabs = numtabs + 1
    end

    return { anchor = { char = pos }, kind = token_raw.newline, indent_level = numtabs }
end

newline = C(Cp() * S"\n\r" * C(P"\t"^0)) / handle_newlines
-- newline = C(Cp() * (S"\n\r" * C(P"\t"^0)) + C(P"\t"^1)) / handle_newlines

function handle_symbols(pos_start, val)
    return { anchor = { char = pos_start }, kind = "symbol", str = val }
end

grammar.symbol = (Cp() * C((1 - (S"#;()[]{}," + wsp_chars))^1 - grammar.number) / handle_symbols)


function replace_escape(data)
    if data == [[\\]] then return [[\]]
    elseif data == [[\"]] then return[["]]
    elseif data == [[\n]] then return "\n"
    elseif data == [[\r]] then return "\r"
    elseif data == [[\t]] then return "\t"
    end
end

function handle_strings(pos, input_fragment)
    local buffer = { anchor = { char = pos }, kind = "literal", bytes = {} }

    for i=1,#input_fragment do
        buffer["bytes"][i] = string.bytes(input_fragment[i])
    end

    return buffer
end


grammar.tokens = P{
    "tokens",
    -- + V"wsp"
    tokens = lpeg.Ct((V"wsp" + V"string" + V"comment_token" + grammar.symbol + grammar.number + V"list_sep" + V"list_start" + V"list_end" + newline + V"string_character" + V"raw_block_string")^0),

    wsp = S"\t ", -- get_grammar_position(S"\t ", "WHITESPACE")
    comment_token = get_grammar_position(P"#" * (1- P"\n")^0, token_raw.comment_begin),
    raw_block_string = get_grammar_position(P[[""""]], token_raw.blockstring),
    string_character = get_grammar_position(P[["]], token_raw.string_char),
    list_start = get_grammar_position(S"(", token_raw.list_start),
    list_end = get_grammar_position(S")", token_raw.list_end),
    list_sep = get_grammar_position(P";", token_raw.list_sep),
    splice_control = get_grammar_position(P"\\", token_raw.splice_control),

    backslash = P("\\"),
    escape_chars = S([[\abfnrtv]]),
    hex_digits = R"09" * R"AF" * R"af",
    unicode_escape = P"u" * (V"hex_digits")^4^-4,
    escape_sequence = V"backslash" * (V"escape_chars" + V"unicode_escape"),


    slice = P"${" * V"tokens" * P"}",
    backslashes = lpeg.Cs(P[[\\]]) / replace_escape,
    escape = lpeg.Cs(P[[\]] * S[[nrt"]]) / replace_escape,
    string_literal = P[["]] * lpeg.Cs((V"backslashes" + V"escape" + (1 - P[["]]))^1) * (P[["]]),

    string = get_grammar_position(P"\"" * ((1 - (P"\\\\"^0 * P"\\"^1 * P"\"")) + (P"${" * V"tokens" * P"}"))^0 * P"\"", "STRING"),

    -- string = get_grammar_position(P"\"\"" )
}

-- there will be a tokenizing stage and a recursive decent stage
-- tokenizing recognizes symbols, numbers, things that could be list start and end tokens (and produces indent and dedent tokens)
-- and produces a stream of tokens
-- need to include character offset and line information
--
-- then there's a recursive decent stage that looks for things that could be list start and ends and recurses: when it encounters a list start, it
-- will recurse and start parsing the list. it will return a list object once it reaches an end token.
-- will add line number information to the output format.

-- TODO: set up property based testing to make sure this works in everywhere
-- TODO: learn what property based testing is
-- TODO: handle strings, multiline strings, list separators, braces, mixed naked/braced

local function recursive_descent(stream, stream_index, indentation_level, indent_applies)
    -- returns: anything it's constructed, where it left off

    -- print(stream_index, " ", indentation_level, " ", indent_applies)

    -- after you see a newline, check indentation level. begin transforming things here
    -- turn indentations into lists
    -- how do with lua's ipairs?
    -- after you see () things stop mattering
    -- recurse when you go down an indentation level until you start going up
    -- raise hell when delimeters mismatched
    -- just add paren when descending
    -- add paren closes when ascending
    --
    -- also filter out comments

    -- print(inspect(ipairs(stream)))

    -- for i,v in ipairs(stream) do
    --     print(i, v)
    -- end

    local construction = { kind = "list", elements = {} }

    local index = stream_index
    while index < #stream do
        -- print("index before: ", index, " indent applies: ", indent_applies)

        local element = stream[index]

        if stream[index]["kind"] == token_raw.newline and indent_applies then
            -- print("hione", index)
            if element["indent_level"] >= indentation_level then

                local result, newindex = recursive_descent(stream, index+1, element["indent_level"], true)
                result["anchor"] = element["anchor"]
                table.insert(construction["elements"], result)
                index = newindex

            elseif element["indent_level"] < indentation_level then
                -- print(inspect(element["anchor"]))
                construction["endpos"] = element["anchor"]
                return construction, (index+1) -- potential issue? incremented here, and at the end
            end

        elseif element["kind"] == token_raw.list_start then
            local result, newindex = recursive_descent(stream, index+1, indentation_level, false)
            result["anchor"] = element["anchor"]
            table.insert(construction["elements"], result)
            index = newindex

        elseif element["kind"] ==  token_raw.list_end then
            construction["endpos"] =  element["anchor"]
            return construction, (index+1)

        elseif element["kind"] == token_raw.comment_begin then
            -- I don't need to preserve comments, so I can be lazy here and not integrate the
            -- parser into the recursive descent bits.
            -- may have to refactor this to properly handle docstrings.

            while index < #stream do
                local element = stream[index]
                if (element["kind"] == token_raw.newline) then
                    if (element["indent_level"] <= indentation_level) then
                        -- print(element)
                        break
                    else
                        index = index + 1
                    end
                else
                    index = index + 1
                end
            end
        else
            table.insert(construction["elements"], element)
            index = index + 1
        end

        -- print("index after: ", index)
    end

    construction["endpos"] = stream[#stream]["anchor"]
    return construction, index
end

function grammar.parse(input, filename)
    local indentation_level = 0
    local position = 1

    local list = grammar.tokens:match(input)

    local list = grammar.correct_anchors(list, filename)

    -- print("streamlen: ", #list)
    local result, index = recursive_descent(list, position, indentation_level, true)

    result["anchor"] = { sourceid = filename, line = 0, char = 0 }

    return result
end

function grammar.correct_anchors(list, filename)
    local linecounter = 0
    local lastlinepos = 0

    for i,v in ipairs(list) do
        if v["kind"] == token_raw.newline then
            linecounter = linecounter + 1
            lastlinepos = v["anchor"]["char"]
        end

        v["anchor"] = { sourceid = filename, line = linecounter, char = (v["anchor"]["char"] - lastlinepos) }
    end


    -- for i=#list,1,-1 do
    --     if list[i]["kind"] == "NEWLINE" then
    --         table.remove(list, i)
    --     end
    -- end

    return list
end




return grammar
