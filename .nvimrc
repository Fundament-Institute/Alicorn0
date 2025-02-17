" SPDX-License-Identifier: 0BSD
" SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

" You can set |'exrc'| and |:trust| this file, or run |:source| on this file.

:lua << EOF
vim.g.project_path_alicorn = vim.fn.expand("<sfile>:p:h")
local nvim_dir_path = vim.fs.joinpath(vim.g.project_path_alicorn, ".nvim")
vim.opt_global.runtimepath:prepend(nvim_dir_path)
vim.opt_global.runtimepath:append(vim.fs.joinpath(nvim_dir_path, "after"))
EOF
