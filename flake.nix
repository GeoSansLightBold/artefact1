{
  description = "cryptovampire";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

    nixpkgs-vampire.url = "github:NixOS/nixpkgs/e0d5027e8873eaa5e8f74fba39072fcb231f4b4b";

    flake-utils = {
      url = "github:numtide/flake-utils";
    };

    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    treefmt-nix = {
      url = "github:numtide/treefmt-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    vampire-master-src = {
      url = "git+https://github.com/vprover/vampire.git?submodules=1";
      flake = false;
    };
  };

  outputs =
    inputs@{
      self,
      nixpkgs,
      nixpkgs-vampire,
      flake-utils,
      treefmt-nix,
      # fenix,
      rust-overlay,
      vampire-master-src,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        vampire-master-overlay = final: prev: {
          vampire = prev.vampire.overrideAttrs (oldAttrs: {
            src = vampire-master-src;
          });
        };
        vampire-4-overlay = final: prev: {
          vampire = pkgs-vampire.vampire;
        };
        overlays = [
          (import rust-overlay)
          vampire-4-overlay # <- comment this out to use Vampire 5.**
          # vampire-master-overlay # <- use this to use Vampire for the master branch
        ];
        pkgs = import nixpkgs {
          inherit system overlays;
        };
        pkgs-vampire = import nixpkgs-vampire { inherit system; };
        treefmtEval = treefmt-nix.lib.evalModule pkgs ./nix/fmt.nix;

        rust = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;

        rustPlatform = pkgs.makeRustPlatform {
          cargo = rust;
          rustc = rust;
        };

        pkgConfig = {
          inherit rustPlatform;
          src = ./.;
        };

        cryptovampire = pkgs.callPackage ./crates/cryptovampire/default.nix pkgConfig;
        indistinguishability = pkgs.callPackage ./crates/indistinguishability/default.nix pkgConfig;

      in
      rec {
        packages = {
          inherit cryptovampire indistinguishability;
          default = indistinguishability;
        };
        # checks =
        #   let
        #     checks = pkgs.callPackage ./nix/check.nix {
        #       inherit cryptovampire treefmtEval;
        #       flake = self;
        #     };
        #     cleanUp =
        #       checks:
        #       builtins.removeAttrs checks [
        #         "override"
        #         "overrideDerivation"
        #       ];
        #   in
        #   cleanUp checks;

        formatter = treefmtEval.config.build.wrapper;

        devShells.default = pkgs.callPackage ./nix/shell.nix ({
          inherit
            cryptovampire
            indistinguishability
            rust
            rustPlatform
            ;
        });

        apps = rec {
          default = indistinguishability;
          cryptovampire = flake-utils.lib.mkApp { drv = packages.cryptovampire; };
          indistinguishability = flake-utils.lib.mkApp { drv = packages.indistinguishability; };
        };
      }
    );

}
