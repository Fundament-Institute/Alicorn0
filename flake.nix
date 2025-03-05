# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

{
  description =
    "An experimental language for high performance safe convenient metaprogramming";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-24.11";
    pre-commit-hooks.inputs.nixpkgs.follows = "nixpkgs";
    pre-commit-hooks.url = "github:cachix/pre-commit-hooks.nix";
    rust-overlay.inputs.nixpkgs.follows = "nixpkgs";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };

  outputs = { flake-utils, nixpkgs, ... }@inputs:
    let
      inherit (nixpkgs) lib;
      luvitOverlay = final: prev: {
        fetchLitDeps = final.callPackage ./nix/fetchLitDeps { };
        luvi = final.callPackage ./nix/luvi { };
        luvit = final.callPackage ./nix/luvit { };
        luvit-lit = final.callPackage ./nix/luvit-lit { };
        makeLitPackage = final.callPackage ./nix/makeLitPackage { };
        makeLuviScript = name: source:
          final.writeScriptBin name "${final.luvi}/bin/luvi ${source} -- $@";
        luvi-prefix = final.writeScript "luvi-prefix" ''
          #!${final.luvi}/bin/luvi --
        '';
      };
      lqc = { argparse, buildLuarocksPackage, fetchFromGitHub, luafilesystem, ... }: buildLuarocksPackage rec {
        pname = "lua-quickcheck";
        version = "0.2-4";
        src = fetchFromGitHub {
          owner = "luc-tielen";
          repo = "lua-quickcheck";
          rev = "v${version}";
          hash = "sha256-B3Gz0emI3MBwp2Bg149KU02RlzVzbKdVPM+B7ZFH+80";
        };
        knownRockspec = "${src}/rockspecs/lua-quickcheck-${version}.rockspec";
        propagatedBuildInputs = [ luafilesystem argparse ];
      };
      perSystem = system:
        let
          pkgs = import inputs.nixpkgs {
            inherit system;
            overlays = [
              luvitOverlay
              inputs.rust-overlay.overlays.rust-overlay
              (pkgsFinal: _pkgsPrev: {
                luajit_lua5_2 = pkgsFinal.luajit.override { enable52Compat = true; self = pkgsFinal.luajit_lua5_2; };
                luajitLua52Packages = pkgsFinal.recurseIntoAttrs pkgsFinal.luajit_lua5_2.pkgs;
              })
            ];
            config = { };
          };

          alicorn-check = file: pkgs.runCommandNoCC "alicorn-check-${file}" { src = ./.; } ''
            set -euo pipefail
            cd -- "$src"
            mkdir -p "$out"
            >&2 echo "Checking "${lib.escapeShellArg file}
            ${lib.escapeShellArg (lib.getExe pkgs.luvit)} ${lib.escapeShellArg file}
          '';
          pre-commit-hooks-lib = inputs.pre-commit-hooks.lib.${system};
          currentSystem =
            {
              checks = {
                terms = alicorn-check "test-terms.lua";
                derive-pretty-print = alicorn-check "test-derive-pretty-print.lua";
                formatting = pkgs.runCommandLocal "stylua-check" { } ''
                  cd ${./.}
                  mkdir $out
                  ${pkgs.lib.getExe pkgs.stylua} . -c
                '';
                reuse-lint = pkgs.runCommandNoCCLocal "reuse-lint" { } ''
                  cd ${./.}
                  ${lib.getExe pkgs.reuse} lint && mkdir $out
                '';
                pre-commit-check = pre-commit-hooks-lib.run {
                  src = ./.;
                  hooks = {
                    statix.enable = true;
                    nixpkgs-fmt.enable = true;
                    stylua.enable = true;
                    stylua.excludes = [ "libs/" "vendor/" ];
                    deadnix.enable = true;
                    deadnix.settings.noLambdaArg = true;
                    deadnix.settings.noLambdaPatternNames = true;
                  };
                };
              };
              # nix fmt's docs say this should only be for *.nix files but we're ignoring that as that's inconvenient
              # See https://github.com/NixOS/nix/issues/9132#issuecomment-1754999829
              formatter = pkgs.writeShellApplication {
                name = "run-formatters";
                runtimeInputs = [ pkgs.deadnix pkgs.nixpkgs-fmt pkgs.statix pkgs.stylua ];
                text = ''
                  set -xeu
                  nixpkgs-fmt "$@"
                  stylua "$@"
                  statix check "$@"
                  deadnix -lL "$@"
                '';
              };
              devShells.alicorn-generic = pkgs.callPackage
                ({ deadnix, inferno, lua-language-server, mkShell, nixpkgs-fmt, reuse, rust-bin, statix, stylua, ... }:
                  mkShell {
                    buildInputs = [
                      deadnix
                      inferno
                      lua-language-server
                      nixpkgs-fmt
                      reuse
                      (rust-bin.fromRustupToolchainFile ./rust-toolchain.toml)
                      statix
                      stylua
                    ];
                    shellHook = ''${currentSystem.checks.pre-commit-check.shellHook}'';
                  })
                { };
              devShells.alicorn-luajit = pkgs.callPackage
                ({ luajit_lua5_2, mkShell, ... }:
                  mkShell {
                    inputsFrom = [ currentSystem.devShells.alicorn-generic ];
                    buildInputs = [
                      (luajit_lua5_2.withPackages (ps: [
                        ps.inspect
                        ps.lpeg
                        (ps.callPackage lqc { })
                        ps.luasocket
                        ps.luaunit
                        ps.tl
                      ]))
                    ];
                  })
                { };
              devShells.alicorn-luvit = pkgs.callPackage
                ({ luvit, luvit-lit, mkShell, ... }:
                  mkShell {
                    inputsFrom = [ currentSystem.devShells.alicorn-generic ];
                    buildInputs = [ luvit luvit-lit ];
                  })
                { };
              devShells.alicorn = currentSystem.devShells.alicorn-luajit;
              devShells.default = currentSystem.devShells.alicorn;
              legacyPackages.nixpkgs = lib.dontRecurseIntoAttrs pkgs;
            };
        in
        currentSystem;
    in
    flake-utils.lib.eachDefaultSystem perSystem;
}
