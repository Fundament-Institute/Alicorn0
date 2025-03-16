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
    luvit-nix.url = "github:aiverson/luvit-nix";
    luvit-nix.inputs.nixpkgs.follows = "nixpkgs";
    luvit-nix.inputs.flake-utils.follows = "flake-utils";
  };

  outputs = { flake-utils, nixpkgs, luvit-nix, ... }@inputs:
    let
      inherit (nixpkgs) lib;
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
    in
    flake-utils.lib.eachDefaultSystem (system:
      let
        inherit (luvit-nix.packages.${system}) luvit lit;
        pkgs = import inputs.nixpkgs {
          inherit system;
          overlays = [
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
          ${lib.escapeShellArg (lib.getExe luvit)} ${lib.escapeShellArg file}
        '';
      in
      rec {
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
          pre-commit-check = inputs.pre-commit-hooks.lib.${system}.run {
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
        devShells.alicorn-generic = pkgs.mkShell {
          inherit (checks.pre-commit-check) shellHook;
          buildInputs = [
            pkgs.deadnix
            pkgs.inferno
            pkgs.lua-language-server
            pkgs.nixpkgs-fmt
            pkgs.reuse
            (pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml)
            pkgs.statix
            pkgs.stylua
          ];
        };
        devShells.alicorn-luajit = pkgs.mkShell {
          inherit (checks.pre-commit-check) shellHook;
          inputsFrom = [ devShells.alicorn-generic ];
          buildInputs = [
            (pkgs.luajit_lua5_2.withPackages (ps: [
              ps.inspect
              ps.lpeg
              (ps.callPackage lqc { })
              ps.luasocket
              ps.luaunit
              ps.tl
            ]))
          ];
        };
        devShells.alicorn-luvit = pkgs.mkShell {
          inherit (checks.pre-commit-check) shellHook;
          inputsFrom = [ devShells.alicorn-generic ];
          buildInputs = [ luvit lit ];
        };
        devShells.alicorn = devShells.alicorn-luajit;
        devShells.default = devShells.alicorn;
        legacyPackages.nixpkgs = lib.dontRecurseIntoAttrs pkgs;
      });
}
