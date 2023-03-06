{
  description = "oak";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-22.11";
    flake-utils.url = "github:numtide/flake-utils";
    gomod2nix.url = "github:nix-community/gomod2nix";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };
  outputs = { self, nixpkgs, flake-utils, gomod2nix, rust-overlay }:
    (flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [
              gomod2nix.overlays.default
              rust-overlay.overlays.default
            ];
            config = {
              android_sdk.accept_license = true; # accept all of the sdk licenses
              allowUnfree = true; # needed to get android stuff to compile
            };
          };
        in
        {
          packages = { };
          devShells = rec {
            rust = with pkgs; mkShell {
              packages = [
                (rust-bin.selectLatestNightlyWith (toolchain: toolchain.default.override {
                  extensions = [
                    "clippy"
                    "llvm-tools-preview"
                    "rust-src"
                    "rustfmt"
                  ];
                  targets = [
                    "wasm32-unknown-unknown"
                    "x86_64-unknown-linux-musl"
                    "x86_64-unknown-none"
                  ];
                }))
                cargo-deadlinks
                cargo-binutils
                cargo-deny
                cargo-nextest
                cargo-udeps
                protobuf
                qemu_kvm
              ];
            };
            lint = with pkgs; mkShell {
              packages = [
                hadolint
                cargo-deadlinks
                nodePackages.prettier
                nodePackages.prettier-plugin-toml
                nixpkgs-fmt
              ];
            };
            bazel = with pkgs; mkShell {
              shellHook = ''
                export ANDROID_BASE_DIR=$(dirname $(dirname $(which android)))
                export ANDROID_HOME=$ANDROID_BASE_DIR/libexec/android-sdk
              '';
              packages = [
                jdk11
                bazel_6
                (androidenv.composeAndroidPackages {
                  includeNDK = false;
                  platformVersions = [ "30" "32" ];
                  buildToolsVersions = [ "30.0.0" ];
                }).androidsdk
              ];
            };
            default = with pkgs; mkShell {
              inputsFrom = [
                rust
                bazel
                lint
              ];
            };
          };
        }));
}
