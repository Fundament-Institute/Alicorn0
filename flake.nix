# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2025 Fundament Software SPC <https://fundament.software>

{
  description =
    "An experimental language for high performance safe convenient metaprogramming";

  inputs = {
    by-name.url = "github:bb010g/by-name.nix";
    by-name.inputs.nixpkgs-lib.follows = "nixpkgs";
    nixpkgs.url = "github:nixos/nixpkgs/nixos-24.11";
    pre-commit-hooks.url = "github:cachix/pre-commit-hooks.nix";
    pre-commit-hooks.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = inputs:
    let
      inherit (inputs) self;
      inherit (inputs.nixpkgs) lib;
      inherit (lib.attrsets) genAttrs;
      allSystems = genAttrs systems (system: perSystem allSystemArgs.${system});
      allSystemArgs = genAttrs systems perSystemArgs;
      byNameLib = inputs.by-name.libs.default;
      importCell = table@{ directoryEntry, ... }: import directoryEntry.path table;
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
      perSystem = { currentSystem, pkgs, pre-commit-hooks-lib, ... }: {
        checks = {
          terms = pkgs.alicorn-check "test-terms.lua";
          derive-pretty-print = pkgs.alicorn-check "test-derive-pretty-print.lua";
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
          ({ deadnix, inferno, lua-language-server, mkShell, nixpkgs-fmt, reuse, statix, stylua, ... }:
            mkShell {
              buildInputs = [
                deadnix
                inferno
                lua-language-server
                nixpkgs-fmt
                reuse
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
      perSystemArgs = system: {
        inherit system;
        currentSystem = allSystems.${system};
        pkgs = import inputs.nixpkgs {
          inherit system;
          overlays = [
            table.rows.luvit.nixpkgsOverlay
            (pkgsFinal: pkgsPrev: {
              alicorn-check = pkgsFinal.callPackage
                ({ lib, luvit, runCommandLocal, ... }: file: runCommandLocal "alicorn-check-${file}" { src = ./.; } ''
                  set -euo pipefail
                  cd -- "$src"
                  mkdir -p "$out"
                  >&2 echo "Checking "${lib.escapeShellArg file}
                  ${lib.escapeShellArg (lib.getExe luvit)} ${lib.escapeShellArg file}
                '')
                { };
              luajit_lua5_2 = pkgsFinal.luajit.override { enable52Compat = true; self = pkgsFinal.luajit_lua5_2; };
              luajitLua52Packages = pkgsFinal.recurseIntoAttrs pkgsFinal.luajit_lua5_2.pkgs;
            })
          ];
          config = { };
        };
        pre-commit-hooks-lib = inputs.pre-commit-hooks.lib.${system};
      };
      systems = lib.systems.flakeExposed;
      table = byNameLib.filesystem.readNameBasedTableDirectory {
        rowFromFile."nixpkgs-overlay.nix" = table: { nixpkgsOverlay = importCell table; };
        rowFromFile."nixpkgs-package.nix" = table: { nixpkgsPackage = importCell table; };
        rowsPath = ./nix;
        specialColumns.input = inputs;
      };
      transposition = byNameLib.attrsets.mapAttrs
        (attrName: attrConfig: byNameLib.attrsets.mapAttrs
          (system: currentSystem: currentSystem.${attrName} or (abort ''
            Could not find `perSystem` attribute `${byNameLib.strings.escapeNixIdentifier attrName}` for system `${byNameLib.strings.escapeNixIdentifier system}`. It is required to declare such an attribute whenever `transposition.${byNameLib.strings.escapeNixIdentifier attrName}` is defined.
          ''))
          allSystems)
        transpositionConfig;
      transpositionConfig.checks = { };
      transpositionConfig.devShells = { };
      transpositionConfig.formatter = { };
      transpositionConfig.legacyPackages = { };
    in
    transposition // { };
}
