# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>
{ system ? builtins.currentSystem }:
let flake = builtins.getFlake (toString ./.);
in flake.checks.${system} // { recurseForDerivations = true; }
