A nonstandard library for Cubical Agda
======================================

An experiment in expressivity.


## Getting started

- The [README folder](https://github.com/cubical-mini/core/tree/master/doc/README) mirrors the structure of the main library.

- Clickable HTML coming soon.


## Building, installing and developing

### nix way
`nix build`, `nix build .#doc`, `nix build .#test` and `nix develop` work as usual. 

### standard way
To build the library run `agda --build-library` in the repo root directory.
Running this command in `doc` or `test` directories partially builds documentation and tests.

For installation instructions please consult [Agda docs](https://agda.readthedocs.io/en/latest/tools/package-system.html).
