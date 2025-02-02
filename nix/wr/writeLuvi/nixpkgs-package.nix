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
