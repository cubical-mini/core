{ agdaPackages
, lib
, ...
}:
agdaPackages.mkDerivation {
  pname = "cm-core";
  version = "0.0.1";

  # TODO: find out what's this
  # src = cleanSourceWith {
  #   !(hasSuffix ".nix" name)
  #   src = ./.;
  # };
  src = ./.;

  # NOTE: https://github.com/agda/agda/pull/7682 has problems with infective
  # imports, thats why we have to pass all those arguments to agda
  buildPhase = ''
    agda \
      --cubical \
      --erasure \
      --erased-matches \
      --guardedness \
      --build-library
  '';

  # 7.
  meta = {
    description = "A nonstandard library for Cubical Agda";
    longDescription = ''
      Some description of cm-core.

      Potentially spanning multiple lines.
    '';
    platforms = lib.platforms.all;
    license = lib.licenses.agpl3Only;
  };
}
