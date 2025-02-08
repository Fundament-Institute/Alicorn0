-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

---@meta

---@param subject_type_a flex_value
---@param l_ctx TypecheckingContext
---@param subject_type_b flex_value
---@param r_ctx TypecheckingContext
---@param subject_value flex_value
---@return boolean ok
---@return flex_value[]|string tuple_types_a
---@return flex_value[] tuple_types_b
---@return flex_value[] tuple_vals
---@return integer n_elements
function infer_tuple_type_unwrapped2(subject_type_a, l_ctx, subject_type_b, r_ctx, subject_value) end

return infer_tuple_type_unwrapped2
