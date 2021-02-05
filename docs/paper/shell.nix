{ pkgs ? import <nixpkgs> {}, ... }:
pkgs.mkShell {
  buildInputs = with pkgs; [
    pandoc
    # ~Minimal TeX installation
    (texlive.combine {
      inherit (texlive) scheme-medium enumitem sectsty biblatex biber ifoddpage relsize was;
    })
  ];
}

