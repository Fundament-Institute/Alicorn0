
# Alicorn


This repository is the current development site for Alicorn. 

The plan is to implement a bootstrap interpreter using Lua which will then be used to write the compiler in Alicorn itself (or a bootstrap subset thereof), which will talk with an LLVM interface module written in C++ to produce a complete native, self hosting compiler.

## Windows setup

Open powershell and navigate to the root folder of this repository, then run this command:

```
PowerShell -NoProfile -ExecutionPolicy unrestricted -Command "[Net.ServicePointManager]::SecurityProtocol = 'Tls12'; iex ((new-object net.webclient).DownloadString('https://github.com/luvit/lit/raw/master/get-lit.ps1'))"
```
