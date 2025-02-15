-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

---@meta

local U = {}

---Exists only to prevent tail call optimizations
---@generic T1
---@param a T1
---@return T1
function U.notail(a) end

---Exists only to prevent tail call optimizations
---@generic T1, T2
---@param a T1
---@param b T2
---@return T1
---@return T2
function U.notail(a, b) end

---Exists only to prevent tail call optimizations
---@generic T1, T2, T3
---@param a T1
---@param b T2
---@param c T3
---@return T1
---@return T2
---@return T3
function U.notail(a, b, c) end

---Exists only to prevent tail call optimizations
---@generic T1, T2, T3, T4
---@param a T1
---@param b T2
---@param c T3
---@param d T4
---@return T1
---@return T2
---@return T3
---@return T4
function U.notail(a, b, c, d) end

---Exists only to prevent tail call optimizations
---@generic T1, T2, T3, T4, T5
---@param a T1
---@param b T2
---@param c T3
---@param d T4
---@param e T5
---@return T1
---@return T2
---@return T3
---@return T4
---@return T5
function U.notail(a, b, c, d, e) end

---Exists only to prevent tail call optimizations
---@generic T1, T2, T3, T4, T5, T6
---@param a T1
---@param b T2
---@param c T3
---@param d T4
---@param e T5
---@param f T6
---@return T1
---@return T2
---@return T3
---@return T4
---@return T5
---@return T6
function U.notail(a, b, c, d, e, f) end

---Exists only to prevent tail call optimizations
---@generic T1, T2, T3, T4, T5, T6, T7
---@param a T1
---@param b T2
---@param c T3
---@param d T4
---@param e T5
---@param f T6
---@param g T7
---@return T1
---@return T2
---@return T3
---@return T4
---@return T5
---@return T6
---@return T7
function U.notail(a, b, c, d, e, f, g) end

---Exists only to prevent tail call optimizations
---@generic T1, T2, T3, T4, T5, T6, T7, T8
---@param a T1
---@param b T2
---@param c T3
---@param d T4
---@param e T5
---@param f T6
---@param g T7
---@param h T8
---@return T1
---@return T2
---@return T3
---@return T4
---@return T5
---@return T6
---@return T7
---@return T8
function U.notail(a, b, c, d, e, f, g, h) end

---Exists only to prevent tail call optimizations
---@generic T1, T2, T3, T4, T5, T6, T7, T8, T9
---@param a T1
---@param b T2
---@param c T3
---@param d T4
---@param e T5
---@param f T6
---@param g T7
---@param h T8
---@param i T9
---@return T1
---@return T2
---@return T3
---@return T4
---@return T5
---@return T6
---@return T7
---@return T8
---@return T9
function U.notail(a, b, c, d, e, f, g, h, i) end

return U.notail
