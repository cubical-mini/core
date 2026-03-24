{
  description = "A non-standard library for Cubical Agda";

  inputs = {
    agda.url = "github:agda/agda";
    flake-parts.url = "github:hercules-ci/flake-parts?rev=34fed993f1674c8d06d58b37ce1e0fe5eebcb9f5";
    nixpkgs.url = "github:NixOS/nixpkgs?rev=d351d0653aeb7877273920cd3e823994e7579b0b";
  };

  outputs = inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      perSystem = { pkgs , system, ... }: let
        coreName = "cm-core";
        coreVersion = "0.1.0";

        core = pkgs.agdaPackages.mkDerivation {
          pname = coreName;
          version = coreVersion;
          src = pkgs.lib.fileset.toSource {
            root = ./. ;
            fileset = pkgs.lib.fileset.unions [
              ./cm-core.agda-lib
              ./src
            ];
          };
          buildInputs = [ ];
          meta = {
            description = "cubical-mini core";
          };
        };

        core-doc = pkgs.agdaPackages.mkDerivation {
          pname = coreName + "-doc";
          version = coreVersion;
          src = pkgs.lib.fileset.toSource {
            root = ./doc ;
            fileset = pkgs.lib.fileset.unions [
              ./doc
            ];
          };
          buildInputs = [ core ];
          meta = {
            description = "cubical-mini core documentation";
          };
        };

        core-test = pkgs.agdaPackages.mkDerivation {
          pname = coreName + "-test";
          version = coreVersion;
          src = pkgs.lib.fileset.toSource {
            root = ./test ;
            fileset = pkgs.lib.fileset.unions [
              ./test
            ];
          };
          buildInputs = [ core core-doc ];
          meta = {
            description = "cubical-mini core test suite";
          };
        };

      in {
        _module.args.pkgs = import inputs.nixpkgs {
          inherit system;
          overlays = [ inputs.agda.overlays.default ];
        };

        packages = {
          default = core;
          doc = core-doc;
          test = core-test;
        };

        devShells.default = pkgs.mkShell {
          packages = [
            pkgs.emacs
            pkgs.haskellPackages.fix-whitespace
            (pkgs.agda.withPackages (p: [ core core-doc core-test ]))
          ];
        };

        checks.default = core-test;
      };

      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
    };
}
