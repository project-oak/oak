{
  description = "oak";
  inputs = {
    systems.url = "github:nix-systems/default";
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
            config = {
              android_sdk.accept_license = true; # accept all of the sdk licenses
              allowUnfree = true; # needed to get android stuff to compile
            };
          };
          inherit (pkgs) lib stdenv;
          androidSdk =
            (pkgs.androidenv.composeAndroidPackages {
              platformVersions = [ "30" ];
              buildToolsVersions = [ "30.0.0" ];
              includeEmulator = false;
              includeNDK = false;
              includeSources = false;
              includeSystemImages = false;
            }).androidsdk;
          rustToolchain =
            # This should be kept in sync with the value in bazel/rust/defs.bzl
            pkgs.rust-bin.nightly."2024-11-01".default.override {
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
                envsubst
                fd
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
                protobuf
                buf # utility to convert binary protobuf to json; for breaking change detection.
                qemu_kvm
                python312
                wasm-pack
              ]
              ++
              # Linux-specific dependencies.
              lib.optionals stdenv.isLinux [
                systemd
              ];
            };
            # Minimal shell with only the dependencies needed to run the format and check-format
            # steps.
            lint = with pkgs; mkShell {
              packages = [
                bazel-buildtools
                cargo-deadlinks
                clang-tools
                go-toml
                hadolint
                ktfmt
                ktlint
                nixpkgs-fmt
                nodePackages.prettier
                nodePackages.markdownlint-cli
                shellcheck
              ];
            };
            # Minimal shell with only the dependencies needed to run the bazel steps.
            bazelShell = with pkgs; mkShell {
              shellHook = ''
                export ANDROID_HOME="${androidSdk}/libexec/android-sdk"
                export GRADLE_OPTS="-Dorg.gradle.project.android.aapt2FromMavenOverride=${androidSdk}/libexec/android-sdk/build-tools/28.0.3/aapt2";

                # Prevent issues when trying to do nix builds inside of a nix shell.
                # https://github.com/NixOS/nix/issues/262
                unset TMPDIR
              '';
              packages = [
                autoconf
                autogen
                automake
                jdk17_headless
                bazel_7
                androidSdk
                bazel-buildtools
              ];
            };
            # Shell for building containers system image. This is not included in the
            # default shell because it is not needed as part of the CI.
            containers = with pkgs; mkShell {
              inputsFrom = [
                base
                bazelShell
                rust
              ];
              packages = [
                bc
                bison
                cpio
                curl
                docker
                fakeroot
                flex
                jq
                libelf
                perl
                strip-nondeterminism
                ncurses
                netcat
                umoci
              ] 
              ++ 
              # Linux-specific dependencies.
              lib.optionals stdenv.isLinux [
                elfutils
                glibc
                glibc.static
              ];
            };
            # Shell for most CI steps (i.e. without containers support).
            ci = pkgs.mkShell {
              inputsFrom = [
                rust
                bazelShell
                lint
              ];
            };
            # This is the shell used by the build scripts executed by GitHub jobs.
            githubBuildShell = pkgs.mkShell {
              packages = [ ];
              inputsFrom = [
                containers
                rust
                bazelShell
              ];
            };
            # By default create a shell with all the inputs.
            default = pkgs.mkShell {
              packages = [ ];
              inputsFrom = [
                containers
                rust
                bazelShell
                lint
              ];
            };
          };
        }));
}
