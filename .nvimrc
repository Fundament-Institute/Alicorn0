" SPDX-License-Identifier: 0BSD
" SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

" You can set |'exrc'| and |:trust| this file, or run |:source| on this file.

:lua << EOF
local nvim_dir_path = vim.fs.joinpath(vim.fn.expand("<sfile>:p:h"), ".nvim")
vim.opt_global.runtimepath:prepend(nvim_dir_path)
vim.opt_global.runtimepath:append(vim.fs.joinpath(nvim_dir_path, "after"))
EOF
