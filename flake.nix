# SPDX-FileCopyrightText: 2021 Serokell <https://serokell.io/>
#
# SPDX-License-Identifier: CC0-1.0

{
  description = "My haskell application";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    monadic-bang.url = "github:JakobBruenker/monadic-bang";
    monadic-bang.flake = false;
  };

  outputs = { self, nixpkgs, flake-utils, monadic-bang }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        #haskellPackages = pkgs.haskell.packages.ghc944;
        haskellPackages = pkgs.haskellPackages;

        jailbreakUnbreak = pkg:
          pkgs.haskell.lib.doJailbreak (pkg.overrideAttrs (_: { meta = { }; }));

        # DON'T FORGET TO PUT YOUR PACKAGE NAME HERE, REMOVING `throw`
        packageName = "abs";
      in {
        packages.${packageName} =
          haskellPackages.callCabal2nix packageName self {
            # Dependency overrides go here
#            monadic-bang = pkgs.haskell.lib.dontCheck (haskellPackages.callCabal2nix "monadic-bang" monadic-bang {fused-effects = pkgs.haskell.lib.dontCheck haskellPackages.fused-effects;});
          };

        packages.default = self.packages.${system}.${packageName};
        defaultPackage = self.packages.${system}.default;

        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            haskellPackages.haskell-language-server # you must build it with your ghc to work
            ghcid
            cabal-install
          ];
          inputsFrom = map (__getAttr "env") (__attrValues self.packages.${system});
        };
        devShell = self.devShells.${system}.default;
      });
}
