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

        minimalFS = [
          ./cm-core.agda-lib
          ./src
        ];

        mkCore = extraFS: pkgs.agdaPackages.mkDerivation {
          pname = "cm-core";
          version = "0.1.0";
          src = pkgs.lib.fileset.toSource {
            root = ./. ;
            fileset = pkgs.lib.fileset.unions (minimalFS ++ extraFS);
          };
          meta.description = "cubical-mini core library";
        };

      in {
        _module.args.pkgs = import inputs.nixpkgs {
          inherit system;
          overlays = [ inputs.agda.overlays.default ];
        };

        packages = {
          default = mkCore [];
          doc = mkCore [ ./extra ];
        };

        devShells.default = pkgs.mkShell {
          packages = [
            forester.packages.${system}.default
            pkgs.agda
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

        # checks.default = core-test;
      };

      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
    };
}
