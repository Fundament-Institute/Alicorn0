# SPDX-License-Identifier: Apache-2.0 OR MIT
# SPDX-FileCopyrightText: 2020 Alex Iverson <alexjiverson@gmail.com>
# SPDX-FileCopyrightText: 2025 Dusk Banks <me@bb010g.com>
{ rows, ... }:
pkgsFinal: pkgsPrev:
{
  fetchLitDeps = pkgsFinal.callPackage rows.fetchLitDeps.nixpkgsPackage { };
  luvi = pkgsFinal.callPackage rows.luvi.nixpkgsPackage { };
  luvi-prefix = pkgsFinal.callPackage rows.luvi-prefix.nixpkgsPackage { };
  luvit = pkgsFinal.callPackage rows.luvit.nixpkgsPackage { };
  luvit-lit = pkgsFinal.callPackage rows.luvit-lit.nixpkgsPackage { };
  makeLitPackage = pkgsFinal.callPackage rows.makeLitPackage.nixpkgsPackage { };
  writeLuvi = pkgsFinal.callPackage rows.writeLuvi.nixpkgsPackage { };
  writeLuviBin = pkgsFinal.callPackage rows.writeLuviBin.nixpkgsPackage { };
}
