# SPDX-License-Identifier: Apache-2.0 OR MIT
# SPDX-FileCopyrightText: 2020 Alex Iverson <alexjiverson@gmail.com>
# SPDX-FileCopyrightText: 2025 Dusk Banks <me@bb010g.com>
{ lib, luvi, luvi-prefix, luvit-lit, stdenv, fetchLitDeps, ... }:
let
  inherit (lib.trivial) isFunction;
  inherit (stdenv) mkDerivation;
  makeLitPackage = fnOrAttrs:
    if isFunction fnOrAttrs then
      makeLitPackageExtensible fnOrAttrs
    else
      makeLitPackageExtensible (finalAttrs: prevAttrs:
        let
          prevMeta = prevAttrs.meta or { };
          attrsMeta = fnOrAttrs.meta or { };
        in
        fnOrAttrs // {
          env = prevAttrs.env or { } // fnOrAttrs.env or { };

          nativeBuildInputs = prevAttrs.nativeBuildInputs or [ ] ++ fnOrAttrs.nativeBuildInputs or [ ];
          buildInputs = prevAttrs.buildInputs or [ ] ++ fnOrAttrs.buildInputs or [ ];

          meta = prevMeta // attrsMeta // {
            passthru = prevMeta.passthru or { } // attrsMeta.passthru or { };
          };
        });
  makeLitPackageExtensible = fnOrAttrs: (mkDerivation (finalAttrs: {
    __structuredAttrs = true;

    deps = fetchLitDeps {
      inherit (finalAttrs) pname version src;
      outputHash = finalAttrs.meta.passthru.depsOutputHash;
    };

    env = {
      inherit (finalAttrs.meta) mainProgram;
    };

    nativeBuildInputs = [ luvi-prefix luvit-lit ];
    buildInputs = [ luvi ];

    buildPhase = ''
      runHook preBuild

      LIT_CONFIG="$PWD/litconfig"
      export LIT_CONFIG
      printf '%s\n' "database: $PWD/.litdb.git" >> "$LIT_CONFIG"

      ln -st ./deps "$deps/deps"

      lit make . "./$mainProgram" "${luvi-prefix}" || printf '%s\n' "work around bug" >&2

      runHook postBuild
    '';

    postInstall = ''
      install -Dt "$out/bin" -m 755 -- "./$mainProgram"
    '';

    meta = {
      mainProgram = finalAttrs.pname;
    };
  })).overrideAttrs fnOrAttrs;
in
makeLitPackage
