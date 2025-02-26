-- SPDX-License-Identifier: Apache-2.0
-- SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

---@meta

local U = {}

---@generic T1
---@param bundle { n: 1, [1]: T1 }
---@return T1 a
function U.unpack_bundle(bundle) end

---@generic T1, T2
---@param bundle { n: 2, [1]: T1, [2]: T2 }
---@return T1 a
---@return T2 b
function U.unpack_bundle(bundle) end

---@generic T1, T2, T3
---@param bundle { n: 3, [1]: T1, [2]: T2, [3]: T3 }
---@return T1 a
---@return T2 b
---@return T3 c
function U.unpack_bundle(bundle) end

---@generic T1, T2, T3, T4
---@param bundle { n: 4, [1]: T1, [2]: T2, [3]: T3, [4]: T4 }
---@return T1 a
---@return T2 b
---@return T3 c
---@return T4 d
function U.unpack_bundle(bundle) end

---@generic T1, T2, T3, T4, T5
---@param bundle { n: 5, [1]: T1, [2]: T2, [3]: T3, [4]: T4, [5]: T5 }
---@return T1 a
---@return T2 b
---@return T3 c
---@return T4 d
---@return T5 e
function U.unpack_bundle(bundle) end

---@generic T1, T2, T3, T4, T5, T6
---@param bundle { n: 6, [1]: T1, [2]: T2, [3]: T3, [4]: T4, [5]: T5, [6]: T6 }
---@return T1 a
---@return T2 b
---@return T3 c
---@return T4 d
---@return T5 e
---@return T6 f
function U.unpack_bundle(bundle) end

---@generic T1, T2, T3, T4, T5, T6, T7
---@param bundle { n: 7, [1]: T1, [2]: T2, [3]: T3, [4]: T4, [5]: T5, [6]: T6, [7]: T7 }
---@return T1 a
---@return T2 b
---@return T3 c
---@return T4 d
---@return T5 e
---@return T6 f
---@return T7 g
function U.unpack_bundle(bundle) end

---@generic T1, T2, T3, T4, T5, T6, T7, T8
---@param bundle { n: 8, [1]: T1, [2]: T2, [3]: T3, [4]: T4, [5]: T5, [6]: T6, [7]: T7, [8]: T8 }
---@return T1 a
---@return T2 b
---@return T3 c
---@return T4 d
---@return T5 e
---@return T6 f
---@return T7 g
---@return T8 h
function U.unpack_bundle(bundle) end

---@generic T1, T2, T3, T4, T5, T6, T7, T8, T9
---@param bundle { n: 9, [1]: T1, [2]: T2, [3]: T3, [4]: T4, [5]: T5, [6]: T6, [7]: T7, [8]: T8, [9]: T9 }
---@return T1 a
---@return T2 b
---@return T3 c
---@return T4 d
---@return T5 e
---@return T6 f
---@return T7 g
---@return T8 h
---@return T9 i
function U.unpack_bundle(bundle) end

return U.unpack_bundle
