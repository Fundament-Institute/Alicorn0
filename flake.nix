{
  description =
    "An experimental language for high performance safe convenient metaprogramming";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-23.11";
    nixpkgs-unstable.url = "github:nixos/nixpkgs/nixos-unstable";
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

  outputs = { self, nixpkgs, nixpkgs-unstable, luvitpkgs, flake-utils, pre-commit-hooks }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        pkgs-unstable = nixpkgs-unstable.legacyPackages.${system};
        alicorn-check = file:
          pkgs.runCommandNoCC "alicorn-check-${file}" { } ''
            set -euo pipefail
            cd ${./.}
            mkdir $out
            >&2 echo "Checking ${file}"
            ${pkgs.lib.getExe luvitpkgs.packages.${system}.luvit} ${file}
          '';
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
          formatting = pkgs.runCommandNoCC "stylua-check" { } ''
            cd ${./.}
            mkdir $out
            ${pkgs.lib.getExe pkgs-unstable.stylua} . -c
          '';
          pre-commit-check = pre-commit-hooks.lib.${system}.run {
            src = ./.;
            hooks = {
              statix.enable = true;
              nixpkgs-fmt.enable = true;
              stylua.enable = true;
              deadnix.enable = true;
            };
          };
        };
        # nix fmt's docs say this should only be for *.nix files but we're ignoring that as that's inconvenient
        # See https://github.com/NixOS/nix/issues/9132#issuecomment-1754999829
        formatter = pkgs.writeShellApplication {
          name = "run-formatters";
          runtimeInputs = [ pkgs-unstable.stylua pkgs.nixpkgs-fmt ];
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
              pkgs-unstable.stylua

              (pkgs.luajit.withPackages
                (ps: with ps; [ luasocket lpeg inspect luaunit tl ]))
            ];
            inherit (self.checks.${system}.pre-commit-check) shellHook;
          };
          default = alicorn;
        };
      });
}
