<!--
SPDX-License-Identifier: Apache-2.0
SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>
-->

```lua
vim.opt_global.runtimepath:prepend(vim.fs.normalize(vim.fs.joinpath(vim.fn.getcwd(), 'nvim-site')))
require('treesitter-quickfix').query_name('refactored_functions', vim.tbl_map(function(filename) return { filename = filename, lang = 'lua' } end, vim.fn.glob('**/*.lua', false, true)))
```
