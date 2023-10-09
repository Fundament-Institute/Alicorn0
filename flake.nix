{
  description =
    "An experimental language for high performance safe convenient metaprogramming";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-22.11";
    luvitpkgs = {
      url = "github:aiverson/luvit-nix";
      # inputs.nixpkgs.follows = "nixpkgs";
    };
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, luvitpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        alicorn-check = file: pkgs.runCommandNoCC "alicorn-check-${file}" { } ''
          set -xeuo pipefail
          cd ${./.}
          mkdir $out
          echo "Checking ${file}"
          ${pkgs.lib.getExe luvitpkgs.packages.${system}.luvit} ${file}
        '';
      in
      {
        packages = rec {
          hello = pkgs.hello;
          default = hello;
        };
        apps = rec {
          hello =
            flake-utils.lib.mkApp { drv = self.packages.${system}.hello; };
          default = hello;
        };
        checks = {
          terms = alicorn-check "test-terms.lua";
        };
        devShells = rec {
          alicorn = pkgs.mkShell {
            buildInputs = [
              luvitpkgs.packages.${system}.lit
              luvitpkgs.packages.${system}.luvit
              pkgs.luaformatter

              (pkgs.luajit.withPackages (ps: with ps; [ luasocket lpeg inspect luaunit ]))
            ];
          };
          default = alicorn;
        };
      });
}
