{ ... }:
{ cmake
, fetchFromGitHub
, lib
, # libuv,
  # luajit,
  ninja
, openssl
, pcre
, stdenv
, ...
}:
let
  inherit (lib.strings) cmakeBool cmakeFeature;
in
stdenv.mkDerivation (finalAttrs: {
  pname = "luvi";
  version = "2.14.0";

  src = fetchFromGitHub {
    owner = "luvit";
    repo = "luvi";
    rev = "v${finalAttrs.version}";
    hash = "sha256-c1rvRDHSU23KwrfEAu+fhouoF16Sla6hWvxyvUb5/Kg=";
    fetchSubmodules = true;
  };

  patches = [
    ./_patches/0001-CMake-non-internal-RPATH-cache-variables.patch
    ./_patches/0002-Respect-provided-CMAKE_INSTALL_RPATH.patch
  ];

  nativeBuildInputs = [ cmake ninja ];
  buildInputs = [
    # luajit.pkgs.libluv
    # libuv
    # luajit
    openssl
    pcre
  ];

  cmakeFlags = [
    (cmakeBool "WithLPEG" true)
    (cmakeBool "WithOpenSSL" true)
    (cmakeBool "WithPCRE" true)
    (cmakeBool "WithSharedOpenSSL" true)
    (cmakeBool "WithSharedPCRE" true)
    (cmakeBool "WithSharedLibluv" false)
    (cmakeBool "WithSharedLPEG" false)
    (cmakeBool "WithSharedZLIB" true)
    (cmakeFeature "LUVI_VERSION" finalAttrs.version)
    (cmakeBool "CMAKE_BUILD_WITH_INSTALL_RPATH" false)
    (cmakeBool "CMAKE_INSTALL_RPATH_USE_LINK_PATH" false)
  ];

  postPatch = ''
    printf '%s\n' ${lib.escapeShellArg finalAttrs.version} >> VERSION
  '';

  meta = {
    description = "a lua runtime for applications";
    homepage = "https://github.com/luvit/luvi";
    license = [ lib.licenses.apsl20 ];
    mainProgram = "luvi";
    maintainers = [ /* lib.maintainers.aiverson */ ];
  };
})
