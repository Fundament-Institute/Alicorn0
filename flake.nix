{
  description =
    "An experimental language for high performance safe convenient metaprogramming";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-24.11";
    luvitpkgs = {
      url = "github:aiverson/luvit-nix";
      # inputs.nixpkgs.follows = "nixpkgs";
    };
    flake-utils.url = "github:numtide/flake-utils";
    pre-commit-hooks = {
      url = "github:cachix/pre-commit-hooks.nix";
      inputs.flake-utils.follows = "flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, luvitpkgs, flake-utils, pre-commit-hooks }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        luajit = pkgs.luajit.override {
          self = luajit;
          enable52Compat = true;
        };
        alicorn-check = file:
          pkgs.runCommandNoCC "alicorn-check-${file}" { } ''
            set -euo pipefail
            cd ${./.}
            mkdir $out
            >&2 echo "Checking ${file}"
            ${pkgs.lib.getExe' luvitpkgs.packages.${system}.luvit "luvit"} ${file}
          '';

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

        luajit_lqc = luajit.pkgs.callPackage lqc { };

      in
      {
        packages = rec {
          inherit (pkgs) hello;
          default = hello;
        };
        apps = rec {
          hello =
            flake-utils.lib.mkApp { drv = self.packages.${system}.hello; };
          default = hello;
        };
        checks = {
          terms = alicorn-check "test-terms.lua";
          derive-pretty-print = alicorn-check "test-derive-pretty-print.lua";
          formatting = pkgs.runCommandNoCC "stylua-check" { } ''
            cd ${./.}
            mkdir $out
            ${pkgs.lib.getExe pkgs.stylua} . -c
          '';
          pre-commit-check = pre-commit-hooks.lib.${system}.run {
            src = ./.;
            hooks = {
              statix.enable = true;
              nixpkgs-fmt.enable = true;
              stylua.enable = true;
              stylua.excludes = [ "libs/" "vendor/" ];
              deadnix.enable = true;
            };
          };
        };
        # nix fmt's docs say this should only be for *.nix files but we're ignoring that as that's inconvenient
        # See https://github.com/NixOS/nix/issues/9132#issuecomment-1754999829
        formatter = pkgs.writeShellApplication {
          name = "run-formatters";
          runtimeInputs = [ pkgs.stylua pkgs.nixpkgs-fmt ];
          text = ''
            set -xeu
            nixpkgs-fmt "$@"
            stylua "$@"
          '';
        };
        devShells = rec {
          alicorn = pkgs.mkShell {
            buildInputs = [
              luvitpkgs.packages.${system}.lit
              luvitpkgs.packages.${system}.luvit
              pkgs.stylua
              pkgs.inferno
              pkgs.lua-language-server

              (luajit.withPackages
                (ps: [ ps.luasocket ps.lpeg ps.inspect ps.luaunit ps.tl luajit_lqc ]))
            ];
            shellHook = ''${self.checks.${system}.pre-commit-check.shellHook}'';
          };
          default = alicorn;
        };
      });
}
