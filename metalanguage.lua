local matcher_kinds = {
  Symbol = true,
  Pair = true,
  Nil = true,
  Value = true,
  Reducible = true,
}

local function issymbol(handler)
  return {
    kind = "Symbol",
    handler = handler,
  }
end

local function ispair(handler)
  return {
    kind = "Pair",
    handler = handler
  }
end

local function isnil(handler)
  return {
    kind = "Nil",
    handler = handler
  }
end

local function isvalue(handler)
  return {
    kind = "Value",
    handler = handler
  }
end

local function get_reducer(reducible)
  return getmetatable(reducible.reducible).reducer
end

local function dispatch_reducer(handler_mapping, default, matcher)
  if matcher.kind == "Reducible" then 
    if handler_mapping[get_reducer(matcher)] then
      return handler_mapping[get_reducer(matcher)](matcher)
    else 
      return default(matcher)
    end
  else 
    default(matcher)
  end
end

local function create_reducible(self, handler, ...)
  local funcnew = {
    ...
  }

  setmetatable(funcnew, self.mt)

  local reducible = {
    kind = "Reducible",
    handler = handler,
    reducible = funcnew,
  }

  return reducible
end

local reducer_mt = { __call = create_reducible }

local function reducer(func, name)

  local function funcwrapper(syntax, matcher)
    return func(syntax, matcher, unpack(matcher.reducible))
  end

  local reducer = {
    wrapper = funcwrapper,
    create_reducible = create_reducible
  }

  local funcnew_mt = {
    name = name,
    __index = {
      reduce = funcwrapper,
    },
    reducer = reducer
  }

  reducer.mt = funcnew_mt

  setmetatable(reducer, reducer_mt)

  return reducer
end

local env_mt
env_mt = {
  __add = function(self, other)
    local res = {}
    for k, v in pairs(self.dict) do
      res[k] = v
    end
    for k, v in pairs(other.dict) do
      if res[k] ~= nil then
        error("names in environments being merged must be disjoint, but both environments have " .. k)
      end
      res[k] = v
    end
    return setmetatable({dict = res}, env_mt)
  end,
  __index = {
    get = function(self, name)
      return self.dict[name]
    end,
    without = function(self, name)
      local res = {}
      for k, v in pairs(self.dict) do
        if k ~= name then
          res[k] = v
        end
      end
      return setmetatable({dict = res}, env_mt)
    end
  },
  __tostring = function(self)
    local message = "env{"
    local fields = {}
    for k, v in pairs(self.dict) do
      fields[#fields + 1] = tostring(k) .. " = " .. tostring(v)
    end
    message = message .. table.concat(fields, ", ") .. "}"
    return message
  end
}

local function newenv(dict)
  return setmetatable({dict = dict}, env_mt)
end

local function symbolenvhandler(env, name)
  --print("symbolenvhandler(", name, env, ")")
  local res = env:get(name)
  if res ~= nil then
    return true, res
  else
    return false, "environment does not contain a binding for " .. name
  end
end

local function symbolexacthandler(expected, name)
  if name == expected then
    return true
  else
    return false, "symbol is expected to be exactly " .. expected .. " but was instead " .. name
  end
end

local function accept_handler(data, ...)
  return true, ...
end
local function failure_handler(data, exception)
  return false, exception
end

local function SymbolInEnvironment(syntax, matcher, environment)
  --print("in symbol in environment reducer", matcher.kind, matcher[1], matcher)
  return syntax:match(
    {
      issymbol(symbolenvhandler)
    },
    failure_handler,
    environment
  )
end

local function SymbolExact(syntax, matcher, symbol)
  return syntax:match(
    {
      issymbol(symbolexacthandler)
    },
    failure_handler,
    symbol
  )
end

local symbol_in_environment = reducer(SymbolInEnvironment, "symbol in env")

local symbol_exact = reducer(SymbolExact, "symbol exact")

local syntax_error_mt = {
  __tostring = function(self)
    local message = "Syntax error at anchor " .. (self.anchor and tostring(self.anchor) or "<unknown position>") .. " must be acceptable for one of:\n"
    local options = {}
    for k, v in ipairs(self.matchers) do
        if v.kind == "Reducible" then
          options[k] = v.kind .. ": " .. getmetatable(v.reducible).name
        else
          options[k] = v.kind
        end
    end
    message = message .. "[ " ..  table.concat(options, ", ") .. " ]"
    message = message .. "\nbut was rejected"
    if self.cause then
      message = message .. " because:\n" .. tostring(self.cause)
    end
    return message
  end
}

local function syntax_error(matchers, anchor, cause)
  return setmetatable(
    {
      matchers = matchers,
      anchor = anchor,
      cause = cause
    },
    syntax_error_mt
  )
end

local constructed_syntax_mt = {
  __index = {
    match = function(self, matchers, unmatched, extra)
      if matchers.kind then print(debug.traceback()) end
      local lasterr = nil
      for _, matcher in ipairs(matchers) do
        if self.accepters[matcher.kind] then
          -- print("accepting primitive handler on kind", matcher.kind)
          return self.accepters[matcher.kind](self, matcher, extra)
        elseif matcher.kind == "Reducible" then
          -- print("trying syntax reduction on kind", matcher.kind)
          local res = {matcher.reducible.reduce(self, matcher)}
          if res[1] then
            --print("accepted syntax reduction")
            if not matcher.handler then
              print("missing handler for ", matcher.kind, debug.traceback())
            end
            return matcher.handler(extra, unpack(res, 2))
          end
          --print("rejected syntax reduction")
          lasterr = res[2]
        end
        --print("rejected syntax kind", matcher.kind)
      end
      return unmatched(extra, syntax_error(matchers, self.anchor, lasterr))
    end
  }
}
local function cons_syntax(accepters, anchor, ...)
  return setmetatable({accepters = accepters, anchor = anchor, ...}, constructed_syntax_mt)
end

local pair_accepters = {
  Pair = function(self, matcher, extra)
    return matcher.handler(extra, self[1], self[2])
  end
}

local function pair(anchor, a, b)
  return cons_syntax(pair_accepters, anchor, a, b)
end

local symbol_accepters = {
  Symbol = function(self, matcher, extra)
    return matcher.handler(extra, self[1])
  end
}

local function symbol(anchor, name)
  return cons_syntax(symbol_accepters, anchor, name)
end

local value_accepters = {
  Value = function(self, matcher, extra)
    return matcher.handler(extra, self[1])
  end
}

local function value(anchor, val)
  return cons_syntax(value_accepters, anchor, val)
end

local nil_accepters = {
  Nil = function(self, matcher, extra)
    return matcher.handler(extra)
  end
}

local nilval = cons_syntax(nil_accepters)

local function list(a, ...)
  if a == nil then return nilval end
  return pair(a, list(...))
end

local eval

local vau_mt = {
  __index = {
    apply = function(self, ops, env)
      local bodyenv = self.params:argmatch(ops) + self.envparam:argmatch(env)
      local bodycode = self.body
      local expr
      local res
      while bodycode ~= unit do
        expr, bodycode = bodycode[1], bodycode[2]
        res, bodyenv = eval(expr, bodyenv)
      end
      return {kind = "value", res}
    end

  }
}


local function list_match_pair_handler(rule, a, b)
  --print("list pair handler", a, b, rule)
  local ok, val = a:match({rule}, failure_handler, nil)
  return ok, val, b
end


local function ListMatch(syntax, matcher, ...)
  local args = {}
  local ok, err, val, tail = true, nil, true, nil
  for i, rule in ipairs({...}) do
    ok, val, tail =
      syntax:match(
        {
          ispair(list_match_pair_handler)
        },
        failure_handler,
        rule
      )
    --print("list match rule", ok, val, tail)
    if not ok then return false, val end
    args[#args + 1] = val
    syntax = tail
  end
  ok, err =
    syntax:match(
      {
        isnil(accept_handler)
      },
      failure_handler,
      nil
    )
  if not ok then return false, err end
  return true, unpack(args)
end

local listmatch = reducer(ListMatch, "list")

local function ListTail(syntax, _, ...)
  local args = {}
  local ok, err, val, tail = true, nil, true, nil
  for i, rule in ipairs({...}) do
    ok, val, tail =
      syntax:match(
        {
          ispair(list_match_pair_handler)
        },
        failure_handler,
        rule
      )
    --print("list+tail match rule", ok, val, tail)
    if not ok then return false, val end
    args[#args + 1] = val
    syntax = tail
  end
  return true, unpack(args), tail
end

local listtail = reducer(ListTail, "list+tail")

local list_many

local function list_many_pair_handler(rule, a, b)
  local ok, val = a:match({rule}, failure_handler, nil)
  if not ok then return ok, val end
  return ok, true, val, b
end

local function list_many_nil_handler()
  return true, false
end

list_many = reducer(function(syntax, _, submatcher)
    local vals = {}
    local ok, cont, val, tail = true, true, nil, syntax
    while ok and cont do
      ok, cont, val, tail = tail:match(
        {
          ispair(list_many_pair_handler),
          isnil(list_many_nil_handler)
        },
        failure_handler,
        submatcher
      )
      vals[#vals + 1] = val
    end
    if not ok then return ok, cont end
    return true, vals
end, "list_many")

oneof = reducer(function(syntax, _, ...)
    return syntax:match({...}, failure_handler, nil)
end, "oneof")

local gen = require './terms-generators'
local constructed_syntax_type = gen.declare_foreign(gen.metatable_equality(constructed_syntax_mt))
local reducer_type = gen.declare_foreign(gen.metatable_equality(reducer_mt))
local matcher_type = gen.declare_foreign(function(val)
  return matcher_kinds[val.kind]
end)

return {
  newenv = newenv,
  accept_handler = accept_handler,
  failure_handler = failure_handler,
  ispair = ispair,
  issymbol = issymbol,
  isvalue = isvalue,
  value = value,
  listmatch = listmatch,
  oneof = oneof,
  listtail = listtail,
  list_many = list_many,
  reducer = reducer,
  isnil = isnil,
  nilval = nilval,
  symbol_exact = symbol_exact,
  pair = pair,
  list = list,
  symbol = symbol,
  symbol_in_environment = symbol_in_environment,
  constructed_syntax_type = constructed_syntax_type,
  reducer_type = reducer_type,
  matcher_type = matcher_type,
}
