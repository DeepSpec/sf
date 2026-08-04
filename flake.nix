{
  description = "Software Foundations mirror and PDF builder environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config.allowUnfree = true;
        };

        coqEnv = pkgs.coq.withPackages (ps: [
          ps.stdlib
          ps.QuickChick
          ps.VST
        ]);

        pythonEnv = pkgs.python3.withPackages (ps: [ ps.beautifulsoup4 ]);

        texEnv = pkgs.texliveSmall.withPackages (ps: [
          ps.ucs
          ps.preprint
          ps.pmboxdraw
          ps.newunicodechar
          ps.cm-super
        ]);
      in
      {
        devShells.default = pkgs.mkShell {
          packages = [
            coqEnv
            pythonEnv
            texEnv
            pkgs.gnumake
            pkgs.patch
            pkgs.git
          ];
        };
      });
}
