local as = {
  record = function(t, info)
    local idx = t.__index or {}
    t.__index = idx
    local kind = info.kind
    local params = info.params

    local returns = {}
    for i, param in ipairs(params) do
      returns[i] = string.format("self[%q]", param)
    end
    local all_returns = table.concat(returns, ", ")
    local chunk = "return function(self) return true, " .. all_returns .. " end"

    print("derive as: record chunk: " .. kind)
    print("###")
    print(chunk)
    print("###")

    local compiled, message = load(chunk, "derive-as_record", "t")
    assert(compiled, message)
    idx["as_" .. kind] = compiled()
  end,
  enum = function(t, info)
    local idx = t.__index or {}
    t.__index = idx
    local name = info.name
    local variants = info.variants

    for n, vname in ipairs(variants) do
      local vkind = name .. "_" .. vname
      local vdata = variants[vname]
      local vtype = vdata.type
      local vinfo = vdata.info
      local all_returns
      if vtype == "record" then
      elseif vtype == "unit" then
      else
        error("unknown variant type: " .. vtype)
      end
      local body = string.format(
        "return function(self)\nif self.kind == %q then\nreturn true, self\nend return false, nil\nend",
        vkind
      )
      local compiled, message = load(body, "derive-as_enum", "t")
      assert(compiled, message)
      idx["as_" .. vname] = compiled()
    end
  end,
}


  -- local typed = terms.inferrable_term.typed(terms.value.number_type, gen.declare_array(gen.builtin_number)(), terms.typed_term.literal(terms.value.number(1)))
  -- p(typed)
  -- p(getmetatable(typed))
  -- p(terms.inferrable_term == getmetatable(typed))

return as
