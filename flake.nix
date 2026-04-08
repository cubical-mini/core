{
  description = "A non-standard library for Cubical Agda";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-parts.url = "github:hercules-ci/flake-parts";
    agda = {
      url = "github:cubical-mini/agda?ref=agda-forester";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-parts.follows = "flake-parts";
    };
    forester.url = "sourcehut:~jonsterling/ocaml-forester";
    treelist.url = "github:samtoth/treelist";
  };

  outputs = inputs@{ flake-parts , forester , treelist , ... }:
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
          meta.description = "cubical-mini core";
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
          meta.description = "cubical-mini core documentation";
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
          meta.description = "cubical-mini core test suite";
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
            forester.packages.${system}.default
            (pkgs.agda.withPackages (p: [ core core-doc core-test ]))
            pkgs.bashInteractive
            pkgs.emacs
            pkgs.fswatch
            pkgs.haskellPackages.fix-whitespace
            pkgs.haskellPackages.wai-app-static
            pkgs.tmux
            treelist.packages.${system}.default
          ];
          shellHook = ''
            export PROJECT_ROOT="$PWD"
            exec $PROJECT_ROOT/.devenv/startup.sh
          '';
        };

        checks.default = core-test;
      };

      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
    };
}
