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
    forest-theme = {
      url = "github:cubical-mini/forest-theme?ref=agda-forester";
      flake = false;
    };
    forester.url = "sourcehut:~jonsterling/ocaml-forester";
    treelist.url = "github:samtoth/treelist";
  };

  outputs = inputs@{ flake-parts , forest-theme , forester , treelist , ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      perSystem = { pkgs , system, ... }: let

        name = "cm-core";

        minimalFS = [
          ./cm-core.agda-lib
          ./src
        ];

        mkCore = extraFS: pkgs.agdaPackages.mkDerivation {
          pname = name;
          version = "0.1.0";
          src = pkgs.lib.fileset.toSource {
            root = ./. ;
            fileset = pkgs.lib.fileset.unions (minimalFS ++ extraFS);
          };
          meta.description = "cubical-mini core library";
        };

        minimal = mkCore [];
        extra = mkCore [ ./extra ]; # interactive doc included

        scripts = pkgs.stdenv.mkDerivation {
          name = "${name} scripts";
          src = ./bin ;
          installPhase = ''
            mkdir -p $out/bin
            cp * $out/bin
            chmod +x $out/bin
          '';
        };

        html = pkgs.stdenv.mkDerivation {
          name = "${name} html";
          src = ./.;
          buildInputs = [
            extra
            forester.packages.${system}.default
            pkgs.agda
            scripts
            treelist.packages.${system}.default
          ];
          installPhase = ''
            cp -R "${forest-theme}" theme/
            prepare-output.sh
            agda-gen-everything.sh
            agda-render.sh
            forest-rebuild.sh
            mkdir -p $out/
            cp -R output/core/* $out/
          '';
        };

      in {
        _module.args.pkgs = import inputs.nixpkgs {
          inherit system;
          overlays = [ inputs.agda.overlays.default ];
        };

        packages = {
          default = minimal;
          inherit extra html;
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
            pkgs.ibm-plex
            pkgs.tmux
            scripts
            treelist.packages.${system}.default
          ];
          shellHook = ''
            export PR=$PWD

            $PR/.devenv/startup.sh
          '';
        };

        # checks.default = core-test;
      };

      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
    };
}
