# SPDX-License-Identifier: Apache-2.0 OR MIT
# SPDX-FileCopyrightText: 2020 Alex Iverson <alexjiverson@gmail.com>
# SPDX-FileCopyrightText: 2025 Dusk Banks <me@bb010g.com>
{ cacert, curl, lib, luvit-lit, stdenv, ... }:
let
  inherit (lib.trivial) isFunction;
  inherit (stdenv) mkDerivation;
  fetchLitDeps = fnOrAttrs:
    if isFunction fnOrAttrs then
      fetchLitDepsExtensible fnOrAttrs
    else
      fetchLitDepsExtensible (finalAttrs: prevAttrs:
        let
          prevMeta = prevAttrs.meta or { };
          attrsMeta = fnOrAttrs.meta or { };
        in
        fnOrAttrs // {
          pname = "${fnOrAttrs.pname}-lit-deps";

          env = prevAttrs.env or { } // fnOrAttrs.env or { };

          nativeBuildInputs = prevAttrs.nativeBuildInputs or [ ] ++ fnOrAttrs.nativeBuildInputs or [ ];
          buildInputs = prevAttrs.buildInputs or [ ] ++ fnOrAttrs.buildInputs or [ ];

          meta = prevMeta // attrsMeta // {
            passthru = prevMeta.passthru or { } // attrsMeta.passthru or { };
          };
        });
  fetchLitDepsExtensible = fnOrAttrs: (mkDerivation (finalAttrs: {
    __structuredAttrs = true;

    nativeBuildInputs = [ cacert curl ];
    buildInputs = [ luvit-lit ];

    buildPhase = ''
      runHook preBuild

      HOME="$PWD"
      export HOME
      lit install || printf '%s\n' "work around bug" >&2

      runHook postBuild
    '';

    installPhase = ''
      runHook preInstall

      mkdir -p "$out"
      cp -rt "$out" ./deps

      runHook postInstall
    '';

    outputHashMode = "recursive";
    outputHashAlgo = if finalAttrs.outputHash == "" then "sha256" else null;
    outputHash = "";
  })).overrideAttrs fnOrAttrs;
in
fetchLitDeps
