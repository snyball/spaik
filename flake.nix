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
        mkMusl = extra: crane-lib.buildPackage {
          src = ./.;
          nativeBuildInputs = with pkgs; [
            pkgsCross.musl64.stdenv.cc
            pkgsCross.musl64.libz
            pkgsCross.musl64.xz
          ] ++ build-tools;
          doCheck = false;
          hardeningDisable = ["all"];
          cargoExtraArgs = extra;
          CARGO_BUILD_TARGET = "x86_64-unknown-linux-musl";
          CARGO_BUILD_RUSTFLAGS = "-C target-feature=+crt-static";
          CC_x86_64_unknown_linux_musl = with pkgs.pkgsCross.musl64.stdenv;
            "${cc}/bin/${cc.targetPrefix}cc";
          CARGO_TARGET_X86_64_UNKNOWN_LINUX_MUSL_LINKER = with pkgs.pkgsCross.musl64.stdenv;
            "${cc}/bin/${cc.targetPrefix}cc";
        };
      in
        rec {
          defaultPackage = crane-lib.buildPackage {
            src = ./.;
            nativeBuildInputs = build-tools;
            doCheck = false;
          };
          packages.musl = mkMusl "";
          packages.musl-min = mkMusl "--no-default-features --features serde";
          packages.win64 = crane-lib.buildPackage {
            src = ./.;
            strictDeps = true;
            doCheck = false;
            depsBuildBuild = with pkgs; [
              pkgsCross.mingwW64.stdenv.cc
              pkgsCross.mingwW64.windows.pthreads
            ];
            nativeBuildInputs = with pkgs; [
              wineWow64Packages.stable
              #wineWowPackages.stable
              clang
            ];
            CARGO_BUILD_TARGET = "x86_64-pc-windows-gnu";
          };
          devShell = pkgs.mkShell {
            packages = all;
          };
        }
    );
}
