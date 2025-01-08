{
  description =
    "An experimental language for high performance safe convenient metaprogramming";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-23.11";
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
        luajitWithPackages = luajit.withPackages (ps: with ps; [ luasocket lpeg inspect luaunit tl lqc ]);
        alicorn-host-check =
          pkgs.runCommandNoCC "alicorn-host-check" { } ''
            set -euo pipefail
            cd ${./.}
            mkdir $out
            export LUA_PATH='${luajitWithPackages}/share/lua/5.1/?.lua;./?.lua'
            for file in host-tests/*.lua
            do
              >&2 printf "\033[1;4mChecking $file\033[0m\n"
              case $file in
                (*/test-fitsinto.lua)
                  # these tests don't work yet
                  printf 'skipping!!!\n'
                  ;;
                (*/test.lua)
                  # these tests only work on luajit
                  ${pkgs.lib.getExe' luajitWithPackages "luajit"} "$file"
                  ;;
                (*)
                  ${pkgs.lib.getExe' luvitpkgs.packages.${system}.luvit "luvit"} "$file"
                  ;;
              esac
            done
          '';

        lqc = luajit.pkgs.buildLuarocksPackage rec {
          pname = "lua-quickcheck";
          version = "0.2-4";
          src = pkgs.fetchFromGitHub {
            owner = "luc-tielen";
            repo = "lua-quickcheck";
            rev = "v${version}";
            hash = "sha256-B3Gz0emI3MBwp2Bg149KU02RlzVzbKdVPM+B7ZFH+80";
          };

          knownRockspec = "${src}/rockspecs/lua-quickcheck-${version}.rockspec";

          propagatedBuildInputs =
            [ luajit luajit.pkgs.luafilesystem luajit.pkgs.argparse ];
        };

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
          inherit alicorn-host-check;
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
              (pkgs.lua-language-server.overrideAttrs {
                version = "unstable";
                src = pkgs.fetchFromGitHub {
                  owner = "LuaLS";
                  repo = "lua-language-server";
                  rev = "db667f6db7ea6852d38460a1ed046eb85bb9e5ff";
                  hash = "sha256-ZYaiSBSnO9lPb/5pYa0OiL0KParuMb4/jIBtE3S/Ruo=";
                  fetchSubmodules = true;
                };

              })

              luajitWithPackages
            ];
            shellHook = self.checks.${system}.pre-commit-check.shellHook + ''
              export LUA_PATH='${luajitWithPackages}/share/lua/5.1/?.lua;./?.lua'
            '';
          };
          default = alicorn;
        };
      });
}
