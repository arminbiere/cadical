{
  description = "Simplified Satisfiability Solver";
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
  };
  outputs =
    {
      self,
      nixpkgs,
    }:
    let
      inherit (nixpkgs) lib;
      systems = lib.intersectLists lib.systems.flakeExposed lib.platforms.linux;
      forAllSystems = lib.genAttrs systems;
      nixpkgsFor = forAllSystems (system: nixpkgs.legacyPackages.${system});
      fs = lib.fileset;

      cadical-package =
        {
          stdenv,
          fetchFromGitHub,
          lsd,
        }:
        stdenv.mkDerivation {
          name = "cadical";
          src = fs.toSource {
            root = ./.;
            fileset = fs.unions [
              ./configure
              ./scripts
              ./makefile.in
              ./src
              ./test
              ./VERSION
            ];
          };
          configurePhase = ''./configure --competition'';

          installPhase = ''
            mkdir -p $out/lib
            # once cadiback doesn't need these folders anymore, remove this copy
            rm build/makefile
            cp -r configure src/ build/ $out
            cp build/libcadical.a $out/lib
            mkdir -p $out/include
            cp src/*.hpp $out/include
          '';
        };
    in
    {
      packages = forAllSystems (
        system:
        let
          cadical = nixpkgsFor.${system}.callPackage cadical-package { };
        in
        {
          inherit cadical;
          default = cadical;
        }
      );
    };
}
