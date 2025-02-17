# SPDX-License-Identifier: Apache-2.0 OR MIT
# SPDX-FileCopyrightText: 2020 Alex Iverson <alexjiverson@gmail.com>
# SPDX-FileCopyrightText: 2025 Dusk Banks <me@bb010g.com>
{ ... }:
{ lib, luvi, writers, ... }:
let
  inherit (lib.attrsets) isAttrs isDerivation;
  inherit (lib.meta) getExe;
  interpreter = "${getExe luvi} --";
in
name: argsOrScript:
if isAttrs argsOrScript && !(isDerivation argsOrScript) then
  writers.makeScriptWriter (argsOrScript // { inherit interpreter; }) name
else
  writers.makeScriptWriter { inherit interpreter; } name argsOrScript
