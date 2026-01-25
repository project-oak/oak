{
  description = "oak";
  inputs = {
    systems.url = "github:nix-systems/x86_64-linux";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    flake-utils.inputs.systems.follows = "systems";
    rust-overlay.url = "github:oxalica/rust-overlay";
    rust-overlay.inputs.nixpkgs.follows = "nixpkgs";
    crane.url = "github:ipetkov/crane";
    crane.inputs.nixpkgs.follows = "nixpkgs";
  };
  outputs = { self, systems, nixpkgs, flake-utils, rust-overlay, crane }:
    (flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [
              rust-overlay.overlays.default
            ];
          };
          # Create a bazelisk package that can be called as "bazel".
          bazelisk-as-bazel = pkgs.symlinkJoin {
            name = "bazelisk-as-bazel";
            paths = [ pkgs.bazelisk];
            postBuild = ''
              # Remove the original binary link if you only want the alias
              # or keep it. Here we explicitly create the alias link:
              ln -s $out/bin/bazelisk $out/bin/bazel
            '';
          };
          rustToolchain =
            # This should be kept in sync with the value in bazel/rust/defs.bzl
            pkgs.rust-bin.nightly."2025-03-01".default.override {
              extensions = [
                "clippy"
                "llvm-tools-preview"
                "rust-analyzer"
                "rust-src"
                "rustfmt"
              ];
              targets = [
                "wasm32-unknown-unknown"
                "x86_64-unknown-linux-musl"
                "x86_64-unknown-none"
              ];
            };
          craneLib = (crane.mkLib pkgs).overrideToolchain rustToolchain;
          src = ./.;
        in
        {
          packages = {  };
          formatter = pkgs.nixpkgs-fmt;
          # We define a recursive set of shells, so that we can easily create a shell with a subset
          # of the dependencies for specific CI steps, without having to pull everything all the time.
          #
          # To add a new dependency, you can search it on https://search.nixos.org/packages and add its
          # name to one of the shells defined below.
          devShells = rec {
            # Base shell with shared dependencies.
            base = with pkgs; mkShell {
              packages = [
                cachix
                just
                ps
                which
              ];
            };
            # Minimal shell with only the dependencies needed to run the Rust tests.
            rust = with pkgs; mkShell {
              inputsFrom = [
                base
              ];
              packages = [
                (rust-bin.selectLatestNightlyWith (toolchain: rustToolchain))
                cargo-audit
                cargo-deadlinks
                cargo-binutils
                cargo-deny
                cargo-nextest
                cargo-udeps
                cargo-vet
                systemd
                qemu_kvm
                python312
                wasm-pack
              ];
            };
            # Minimal shell with only the dependencies needed to run the bazel steps.
            bazelShell = with pkgs; mkShell {
              shellHook = ''
                # https://github.com/NixOS/nix/issues/262
                unset TMPDIR

                export BAZELISK_VERIFY_SHA256=d0d3668108c395eee26bd3bd2d251285fdd6dcdd70f22b6c9145e7963ada8e63
              '';
              packages = [
                autoconf
                autogen
                automake
                bazelisk-as-bazel
                bazel-buildtools
              ];
            };
            # By default create a shell with all the inputs.
            default = pkgs.mkShell {
              packages = [];
              inputsFrom = [
                rust
                bazelShell
              ];
            };
          };
        }));
}
