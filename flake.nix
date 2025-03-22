{
  description = "A nonstandard library for Cubical Agda";

  inputs = {
    nixpkgs.url = "nixpkgs/nixos-24.11";
    flake-parts.url = "github:hercules-ci/flake-parts";
  };

  outputs = inputs:
    let
      overlay = final: prev: {
        haskellPackages = prev.haskellPackages.override {
          overrides = hfinal: hprev:
            let
              agdaSrc = {
                src = prev.fetchFromGitHub {
                  owner = "agda";
                  repo = "agda";
                  rev = "33eda29f96f9b8e9e416548961dc7ca2d5ea03b7";
                  hash = "sha256-iCzJZK//IlxNCfJEPY7lR2Q730BbVLDIF5R5M0QLZwM=";
                };
                version = "2.8.0.0a0";
              };
              agdaExtraBuildDepends = with hprev; [
                enummapset
                filemanip
                generic-data
                nonempty-containers
                process-extras
                tasty
                tasty-hunit
                tasty-quickcheck
                tasty-silver
                temporary
                unix-compat
              ];
              # Test suite needs agda executable
              agdaPreCheck = prev.haskell.lib.compose.overrideCabal(drv: {
                preCheck = ''
                  export PATH="$PWD/dist/build/agda:$PATH"
                '' + drv.preCheck or "";
              });
              # Build agda-builtins.agda-lib
              agdaPostInstall = prev.haskell.lib.compose.overrideCabal(drv: {
                postInstall = ''
                  AGDA=$PWD/dist/build/agda/agda
                  pushd $($AGDA --print-agda-data-dir)/lib/prim
                  find . -name '*.agda' -exec $AGDA '{}' ';'
                  popd
                '' + drv.preCheck or "";
              });
              cornelisSrc = {
                src = prev.fetchFromGitHub {
                  owner = "agda";
                  repo = "cornelis";
                  rev = "dca4bda97d6718e76af3f203d688fe6b4a2e9927";
                  hash = "sha256-mV8FVENNzlSJp6J499D/H4DIjgtbQ0Y/xzoLFoQeIIY=";
                };
                version = "2.8.0.0a0";
              };
            in
              {
                Agda = prev.lib.pipe hprev.Agda
                  [ (prev.haskell.lib.compose.overrideSrc agdaSrc)
                    (prev.haskell.lib.compose.addBuildDepends agdaExtraBuildDepends)
                    # NOTE: Tests take hell lot of time
                    # Also some tests fail at the moment
                    prev.haskell.lib.compose.dontCheck
                    # agdaPreCheck
                    agdaPostInstall
                  ];
                cornelis = prev.lib.pipe hprev.cornelis
                  [ (prev.haskell.lib.compose.overrideSrc cornelisSrc)
                  ];
              };
        };
      };
    in
      inputs.flake-parts.lib.mkFlake { inherit inputs; } {
        systems = [
          "x86_64-linux"
          ];

        flake.overlays.default = overlay;

        perSystem = { self', system, pkgs, ...}:
          let
            cm-core = pkgs.callPackage ./cm-core.nix {};
          in
            {
              _module.args.pkgs = import inputs.nixpkgs {
                inherit system;
                overlays = [
                  overlay
                ];
                config = {};
              };

              packages = {
                default = cm-core;
                agda = pkgs.agda;
              };

              devShells.default = pkgs.mkShell {
                buildInputs = with pkgs; [
                  (agda.withPackages [ cm-core ])
                  just
                ];
              };
            };


      };
}
