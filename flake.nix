{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    crane.url = "github:ipetkov/crane";
    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, crane, fenix, flake-utils }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = nixpkgs.legacyPackages.${system};
        manifest = (pkgs.lib.importTOML ./Cargo.toml).package;
        toolchain = fenix.packages.${system}.fromToolchainFile {
          file = ./rust-toolchain.toml;
          sha256 = "sha256-xvsCckp+zh5HvVBArcMaKp7EpMV7i7wtXefh6UNWzcI=";
        };
        crane-lib = (crane.mkLib pkgs).overrideToolchain (p: toolchain);
        wasm-tools = with pkgs; [
          binaryen
          twiggy
          wabt
          wasm-bindgen-cli
          wasmtime
        ];
        build-tools = with pkgs; [ mold toolchain ];
        all = build-tools ++ wasm-tools;
      in
        rec {
          defaultPackage = crane-lib.buildPackage {
            src = ./.;
            nativeBuildInputs = build-tools;
            doCheck = false;
          };
          devShell = pkgs.mkShell {
            packages = all;
          };
        }
    );
}
