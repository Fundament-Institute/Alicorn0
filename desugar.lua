


local syntax_iterator_mt
syntax_iterator_mt = {
  __index = {
    advance = function(self)
      if self.done then return end
      self.idx = self.idx + 1
      if self.slice[self.idx] == nil then
        if self.slice.follow then
          self.slice = self.slice.follow
          self.idx = self.slice.followidx or 1
        else
          self.done = true
        end
      end
    end,
    clone = function(self)
      return setmetatable(
          {
            done = self.done,
            slice = self.slice,
            idx = self.idx
          },
          syntax_iterator_mt
        )
    end,
    peek = function(self)
      if self.done then return end
      return self.slice[self.idx]
    end,
    hasnext = function(self)
      return not self.done
    end
  }
}

local function new_syntax_iterator(syntaxlist)
  return setmetatable(
    {
      done = #syntaxlist == 0,
      slice = syntaxlist,
      idx = 1
    },
    syntax_iterator_mt
  )
end

local syntax_builder_mt = {
  __index = {
    yield = function(self, object) end,
    error = function(self, err) end,
  }
}

--[[

struct Anchor
  sourceid : ByteBuffer
  line : u32
  char : u32

struct SyntaxSlice
  buff : (Buffer SyntaxElement)
  next : (Maybe (Rc this-type))
  nextidx : u32

struct SyntaxIterator
  slice : (Maybe (Rc SyntaxSlice))
  idx : u32


type SemanticNode :
  tuple
    inputlinks = (Buffer (tuple (Rc this-type) u32))
    operation = SemanticOp



type Operator :
  tuple
    args = ArgumentTypes
    implicits = ImplicitDeps
    operation = OperatorDef

enum Expr
  node : SemanticNode
  operator : Operator (Buffer Expr)
  spice : SpiceMacro (Buffer Expr)
  poison

type SugarMacro : ((tuple SyntaxIterator Scope) <-: (SyntaxIterator SyntaxIterator Scope) raises SugarError)

type SpiceMacro : (Expr <-: ((Buffer Expr)) raises SpiceError)

interface SyntaxProcessor
  next : ((Result Expr (tuple SyntaxError this-type)) <-: (this-type))
]]

local function new_syntaxerror(msg, anchor, propagation)
  return {
    msg = msg,
    anchor = anchor,
    propagation
  }
end

local Expr = {
  poison = function(err)
    return {kind = "poison", err = err}
  end
}

local Result = {
  ok = function(val)
    return {kind = "ok", val}
  end,
  err = function(val)
    return {kind = "err", val}
  end
}

local literal_operator = {}

local function literal_to_expr(syntaxliteral)
  return Expr.poison(new_syntaxerror("NYI literals", syntaxliteral.anchor)
end

local SyntaxProcessor_mt = {
  __index = {
    next = function(self)
      while true do
        local topiter = self.syntaxstack[#self.syntaxstack]
        if topiter:hasnext() then
          local next = topiter:peek()
          topiter:advance()
          if head.kind == "symbol" then
            local headexpr = scope:getsym(head.string)
            if not headexpr then
              local err = new_syntaxerror("symbol " .. head.string .. " is not bound in scope", head.anchor)
              table.insert(self.exprstack[#self.exprstack], Expr.poison(err))
              return Result.err{err, self}
            end
            table.insert(self.exprstack[#self.exprstack], headexpr)
          elseif head.kind == "literal" then


            if #self.exprstack[#self.exprstack] == 0 then

            end
          end
        else
          table.remove(self.syntaxstack, -1)

          if #self.syntaxstack == 0 then
            return self.exprstack[1]
          end
        end
      end
    end
  }
}

local function new_SyntaxProcessor(syntaxiterator, scope)
  local self = {
    syntaxstack = {syntaxiterator},
    exprstack = {{}}
  }
end

local SemanticNode_mt = {
  __index = {
    tryeval = function(self)
    end
  }
}

local function spice_resolve(syntax)
end

local function syntax_to_expr(syntax, tailsyntax, scope, allerrors)
  if syntax.kind == "symbol" then
    return scope:getsym(syntax.str), tail, scope
  elseif syntax.kind = "literal" then

  elseif syntax.kind = "list" then
    local iter = new_syntax_iterator(syntax.elements)
    if iter:hasnext() then
      local head = iter:peek()
      iter:advance()
      local tail
      head, tail, scope = syntax_to_expr(head, iter, scope, allerrors)

    while iter:hasnext() do
      local item = iter:peek()


end

local function desugar_all(syntaxlist, scope, allerrors)
  local iter = new_syntax_iterator(syntaxlist)
  local builder = new_syntax_builder()
  while iter:hasnext() do
    local item = iter:peek()
    if item.kind == "list" then
      -- Invocation
      if #item.elements > 0 then
        -- has a lead element
        local head = item.elements[1]
        if head.kind == "list" then
          head, scope = desugar_all(head, scope, allerrors)
        elseif head.kind == "symbol" then
          local sym = head.str
          local val = scope:getsym(sym)
          if not val then
            builder:error(err, {err = "no symbol " .. sym .. " in scope", anchor = item.elements[1].anchor)
          end
