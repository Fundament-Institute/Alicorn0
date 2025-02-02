{ rows, ... }:
{ fetchFromGitHub, lib, luvi, luvi-prefix, stdenv, ... }:
stdenv.mkDerivation (finalAttrs: {
  pname = "lit";
  version = "3.8.5";

  src = fetchFromGitHub {
    owner = "luvit";
    repo = "lit";
    rev = "${finalAttrs.version}";
    hash = "sha256-8Fy1jIDNSI/bYHmiGPEJipTEb7NYCbN3LsrME23sLqQ=";
    fetchSubmodules = true;
  };

  env = {
    inherit (finalAttrs.meta) mainProgram;
  };

  nativeBuildInputs = [ luvi luvi-prefix ];

  buildPhase = ''
    runHook preBuild

    LIT_CONFIG="$PWD/litconfig"
    export LIT_CONFIG
    printf '%s\n' "database: $PWD/.litdb.git" >> "$LIT_CONFIG"

    luvi . -- make . "./$mainProgram" "$(command -v luvi-prefix)" || printf '%s\n' "work around bug" >&2

    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall

    install -Dt "$out/bin" -m 755 -- "./$mainProgram"

    runHook postInstall
  '';

  meta = {
    description = "packaging tool for luvit";
    homepage = "https://github.com/luvit/lit";
    license = [ lib.licenses.apsl20 ];
    mainProgram = finalAttrs.pname;
    maintainers = [ /* lib.maintainers.aiverson */ ];
  };
})
