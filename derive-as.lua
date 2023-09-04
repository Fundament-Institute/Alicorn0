local derive_as = {
    enum = function(t, info)
      local idx = t.__index or {}
      t.__index = idx

      for n, vname in ipairs(info.variants) do
        local body = string.format(
            "return function(self)\nif self.kind == %q then\nreturn true, self\nend return false, nil\nend",
            info.name .. "_" .. vname
        )
        local compiled, message = load(body, "derive-as", "t")
        assert(compiled, message)
        idx['as_' .. vname] = compiled()
      end
    end,
  }


  -- local typed = terms.inferrable_term.typed(terms.value.number_type, gen.declare_array(gen.builtin_number)(), terms.typed_term.literal(terms.value.number(1)))
  -- p(typed)
  -- p(getmetatable(typed))
  -- p(terms.inferrable_term == getmetatable(typed))

return {
  derive_as = derive_as
}