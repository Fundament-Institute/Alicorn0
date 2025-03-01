
# Alicorn


This repository is the current development site for Alicorn. 

The plan is to implement a bootstrap interpreter using Lua which will then be used to write the compiler in Alicorn itself (or a bootstrap subset thereof), which will talk with an LLVM interface module written in C++ to produce a complete native, self hosting compiler.

## Current features

Alicorn is a dependently typed language with universe polymorphism and powerful subtyping. It uses structural typing for the main type combinators and exposes their descriptors in introspectable forms to facilitate typesafe type directed metaprogramming. It also has a novel statically-typed operative system which fulfills a similar role to a macro system in lisp and scheme, but completely replaces any special forms and allows all keyword-equivalents to be expressed and rebound as ordinary expressions. Alicorn is designed to support high performance compilation to a variety of targets, but currently only supports glsl in simple cases and interpretation in Lua. Alicorn has a fluid indentation based syntax for ease of reading and a pure delimiter based syntax optimized for automated tools, which may be freely mixed and interconverted. It supports type families with variances and implicit arguments on functions, including special type families for binding to host types and functions for a foreign function interface.

## Linux setup

Use the provided flake to get dependencies.

```
nix develop
```

To run all available tests, run
```
nix flake check
```

## Windows setup

Open powershell and navigate to the root folder of this repository, then run this command:

```
PowerShell -NoProfile -ExecutionPolicy unrestricted -Command "[Net.ServicePointManager]::SecurityProtocol = 'Tls12'; iex ((new-object net.webclient).DownloadString('https://github.com/luvit/lit/raw/master/get-lit.ps1'))"
```

## Funding

This project is funded through [NGI Zero Core](https://nlnet.nl/core), a fund established by [NLnet](https://nlnet.nl) with financial support from the European Commission's [Next Generation Internet](https://ngi.eu) program, in partnership with the [Feather UI project](https://nlnet.nl/project/FeatherUI).

[<img src="https://nlnet.nl/logo/banner.png" alt="NLnet foundation logo" width="20%" />](https://nlnet.nl)
[<img src="https://nlnet.nl/image/logos/NGI0_tag.svg" alt="NGI Zero Logo" width="20%" />](https://nlnet.nl/core)

## License
Copyright © 2025 Fundament Software SPC

Distributed under the [Apache License, Version 2.0](http://www.apache.org/licenses/LICENSE-2.0).

SPDX-License-Identifier: Apache-2.0
