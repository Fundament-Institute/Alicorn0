-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

---@meta

---@overload fun(inferrable_term : anchored_inferrable, typechecking_context : TypecheckingContext) : boolean, string
---@param inferrable_term anchored_inferrable
---@param typechecking_context TypecheckingContext
---@return boolean ok
---@return flex_value type
---@return ArrayValue<integer> usages
---@return typed term
local function infer(inferrable_term, typechecking_context) end

return infer
