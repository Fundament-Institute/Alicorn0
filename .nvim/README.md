<!--
SPDX-License-Identifier: Apache-2.0
SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>
-->

You can run `|:{range}lua|` on specific lines of this file.

```lua
require("nvim-treesitter-quickfix").query_name(
	"refactored_functions",
	vim.tbl_map(function(filename)
		return { filename = filename, lang = "lua" }
	end, vim.fn.glob("**/*.lua", false, true))
)
```
