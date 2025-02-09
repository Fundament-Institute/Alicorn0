-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

---@meta

---@param val flex_value an alicorn value
---@param usages MapValue<integer, integer> the usages array we are filling
---@param context_len integer number of bindings in the runtime context already used - needed for closures
---@param ambient_typechecking_context TypecheckingContext
---@param gas GasTank? tracks recursive calls
local function gather_usages(val, usages, context_len, ambient_typechecking_context, gas) end

return gather_usages
