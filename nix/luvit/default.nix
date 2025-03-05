# SPDX-License-Identifier: Apache-2.0 OR MIT
# SPDX-FileCopyrightText: 2020 Alex Iverson <alexjiverson@gmail.com>
# SPDX-FileCopyrightText: 2025 Dusk Banks <me@bb010g.com>
{ fetchFromGitHub, lib, makeLitPackage, ... }:
makeLitPackage (finalAttrs: prevAttrs: {
  pname = "luvit";
  version = "unstable-2022-01-19";

  src = fetchFromGitHub {
    owner = "luvit";
    repo = "luvit";
    rev = "3f328ad928eb214f6438dd25fb9ee8b5c1e9255c";
    hash = "sha256-TNiD6GPnS8O2d53sJ52xWYqMAXrVJu2lkfXhf2jWuL0=";
  };

  postPatch = prevAttrs.postPatch or "" + ''
    rm -- ./Makefile
  '';

  meta = prevAttrs.meta or { } // {
    description = "a lua runtime for application";
    homepage = "https://github.com/luvit/luvi";
    license = lib.licenses.apsl20;
    maintainers = [ /* lib.maintainers.aiverson */ ];
    passthru = prevAttrs.meta.passthru or { } // {
      depsOutputHash = "sha256-3EYdIjxF6XvFE3Ft6qpx/gaySMKiZi3kKr2K7QPB+G0=";
    };
  };
})
