{
  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixpkgs-unstable;
    naersk = {
      url = github:nmattia/naersk;
      inputs.nixpkgs.follows = "nixpkgs";
    };
    fenix = {
      url = github:nix-community/fenix;
      inputs.nixpkgs.follows = "nixpkgs";
    };
    flake-utils.url = github:numtide/flake-utils;
  };

  outputs = { self, nixpkgs, naersk, fenix, flake-utils }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = nixpkgs.legacyPackages.${system};
        manifest = (pkgs.lib.importTOML ./Cargo.toml).package;
        toolchain = fenix.packages.${system}.fromToolchainFile {
          file = ./rust-toolchain.toml;
          sha256 = "sha256-AJ6LX/Q/Er9kS15bn9iflkUwcgYqRQxiOIL2ToVAXaU=";
        };
        naersk-lib = naersk.lib.${system}.override {
          cargo = toolchain;
          rustc = toolchain;
        };
        deps = with pkgs; [mold clang toolchain];
        rev = self.rev or self.dirtyRev;
      in
        rec {
          defaultPackage = packages.x86_64-unknown-linux-musl;
          packages.x86_64-unknown-linux-gnu = naersk-lib.buildPackage {
            src = ./.;
            nativeBuildInputs = deps;
          };
          packages.x86_64-unknown-linux-musl = naersk-lib.buildPackage {
            src = ./.;
            nativeBuildInputs = with pkgs; [pkgsStatic.stdenv.cc] ++ deps;
            hardeningDisable = ["all"];
            CARGO_BUILD_TARGET = "x86_64-unknown-linux-musl";
            CARGO_BUILD_RUSTFLAGS = "-C target-feature=+crt-static";
            CARGO_TARGET_X86_64_UNKNOWN_LINUX_MUSL_LINKER = with pkgs.pkgsStatic.stdenv;
              "${cc}/bin/${cc.targetPrefix}gcc";
          };
          devShell = pkgs.mkShell {
            nativeBuildInputs = with pkgs; [
              wasmtime
            ] ++ deps;
          };
        }
    );
}
