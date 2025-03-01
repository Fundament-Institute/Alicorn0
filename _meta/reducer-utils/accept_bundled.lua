-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

---@meta

local U = {}

---@generic T1
---@param a T1
---@return { n: 1, [1]: T1 } bundle
function U.accept_bundled(a) end

---@generic T1, T2
---@param a T1
---@param b T2
---@return { n: 2, [1]: T1, [2]: T2 } bundle
function U.accept_bundled(a, b) end

---@generic T1, T2, T3
---@param a T1
---@param b T2
---@param c T3
---@return { n: 3, [1]: T1, [2]: T2, [3]: T3 } bundle
function U.accept_bundled(a, b, c) end

---@generic T1, T2, T3, T4
---@param a T1
---@param b T2
---@param c T3
---@param d T4
---@return { n: 4, [1]: T1, [2]: T2, [3]: T3, [4]: T4 } bundle
function U.accept_bundled(a, b, c, d) end

---@generic T1, T2, T3, T4, T5
---@param a T1
---@param b T2
---@param c T3
---@param d T4
---@param e T5
---@return { n: 5, [1]: T1, [2]: T2, [3]: T3, [4]: T4, [5]: T5 } bundle
function U.accept_bundled(a, b, c, d, e) end

---@generic T1, T2, T3, T4, T5, T6
---@param a T1
---@param b T2
---@param c T3
---@param d T4
---@param e T5
---@param f T6
---@return { n: 6, [1]: T1, [2]: T2, [3]: T3, [4]: T4, [5]: T5, [6]: T6 } bundle
function U.accept_bundled(a, b, c, d, e, f) end

---@generic T1, T2, T3, T4, T5, T6, T7
---@param a T1
---@param b T2
---@param c T3
---@param d T4
---@param e T5
---@param f T6
---@param g T7
---@return { n: 7, [1]: T1, [2]: T2, [3]: T3, [4]: T4, [5]: T5, [6]: T6, [7]: T7 } bundle
function U.accept_bundled(a, b, c, d, e, f, g) end

---@generic T1, T2, T3, T4, T5, T6, T7, T8
---@param a T1
---@param b T2
---@param c T3
---@param d T4
---@param e T5
---@param f T6
---@param g T7
---@param h T8
---@return { n: 8, [1]: T1, [2]: T2, [3]: T3, [4]: T4, [5]: T5, [6]: T6, [7]: T7, [8]: T8 } bundle
function U.accept_bundled(a, b, c, d, e, f, g, h) end

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
---@return { n: 9, [1]: T1, [2]: T2, [3]: T3, [4]: T4, [5]: T5, [6]: T6, [7]: T7, [8]: T8, [9]: T9 } bundle
function U.accept_bundled(a, b, c, d, e, f, g, h, i) end

return U.accept_bundled
