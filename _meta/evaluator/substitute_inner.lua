-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

---@meta

---@param val flex_value an alicorn value
---@param mappings {[integer]: typed} the placeholder we are trying to get rid of by substituting
---@param mappings_changed boolean whether `mappings` should be used in this substitution
---@param context_len integer number of bindings in the runtime context already used - needed for closures
---@param ambient_typechecking_context TypecheckingContext
---@return typed r a typed term
local function substitute_inner(val, mappings, mappings_changed, context_len, ambient_typechecking_context) end

return substitute_inner
