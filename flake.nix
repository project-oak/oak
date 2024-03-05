{
  description = "oak";
  inputs = {
    systems.url = "github:nix-systems/x86_64-linux";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    flake-utils.inputs.systems.follows = "systems";
    rust-overlay.url = "github:oxalica/rust-overlay";
    rust-overlay.inputs.nixpkgs.follows = "nixpkgs";
    rust-overlay.inputs.flake-utils.follows = "flake-utils";
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
          fff = builtins.fetchurl {
              url = "https://raw.githubusercontent.com/project-oak/oak/d69b46b83337b1e8d78fa9ecb8a42ca06648fa8a/BUILD";
              sha256 = "sha256:1n13phv63245l25vg1dcb7cf9bvxwavygkqmlpxgcgxxzp8199j4";
          };
          ddd = pkgs.stdenv.mkDerivation {
            name = "hello";
            src = builtins.fetchurl {
              url = "https://raw.githubusercontent.com/project-oak/oak/d69b46b83337b1e8d78fa9ecb8a42ca06648fa8a/BUILD";
              sha256 = "sha256:1n13phv63245l25vg1dcb7cf9bvxwavygkqmlpxgcgxxzp8199j4";
            };
            dontUnpack = true;
          };
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
            pkgs.rust-bin.nightly."2023-11-15".default.override {
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
          # Build xtask as a package so that we can use it in the devShell and cache it in the
          # future, without rebuilding it every time.
          xtask = craneLib.buildPackage {
            inherit src;
            pname = "xtask";
            version = "0.1.0";
            cargoExtraArgs = "--package=xtask";
            buildInputs = [
              pkgs.protobuf
            ];
          };
          # Build the dependencies of xtask as a package so that we can use it in the devShell and
          # cache it in the future, without rebuilding it every time.
          cargoDeps = craneLib.buildDepsOnly {
            inherit src;
            pname = "cargodeps";
            version = "0.1.0";
            cargoExtraArgs = "--package=xtask";
          };
        in
        {
          packages = { };
          formatter = pkgs.nixpkgs-fmt;
          # We define a recursive set of shells, so that we can easily create a shell with a subset
          # of the dependencies for specific CI steps, without having to pull everything all the time.
          #
          # To add a new dependency, you can search it on https://search.nixos.org/packages and add its
          # name to one of the shells defined below.
          devShells = rec {
            # Base shell with shared dependencies.
            base = with pkgs; mkShell {
              FOO = fff;
              packages = [
                just
                ps
                which
                # fff
                # ddd
              ];
              shellHook = ''
                source .xtask_bash_completion
              '';
            };
            # Minimal shell with only the dependencies needed to run the Rust tests.
            rust = with pkgs; mkShell {
              inputsFrom = [
                base
              ];
              packages = [
                (rust-bin.selectLatestNightlyWith (toolchain: rustToolchain))
                cargo-deadlinks
                cargo-binutils
                cargo-deny
                cargo-fuzz
                cargo-nextest
                cargo-udeps
                cargo-vet
                protobuf
                systemd
                qemu_kvm
                python312
              ];
            };
            # For some reason node does not know how to find the prettier plugin, so we need to
            # manually specify its fully qualified path.
            prettier = with pkgs; writeShellScriptBin "prettier" ''
              ${nodePackages.prettier}/bin/prettier \
              --plugin "${nodePackages.prettier-plugin-toml}/lib/node_modules/prettier-plugin-toml/lib/index.js" \
              "$@"
            '';
            # Minimal shell with only the dependencies needed to run the format and check-format
            # steps.
            lint = with pkgs; mkShell {
              packages = [
                bazel-buildtools
                cargo-deadlinks
                clang-tools
                hadolint
                nixpkgs-fmt
                nodePackages.markdownlint-cli
                shellcheck
              ];
              buildInputs = [
                prettier
              ];
            };
            # Minimal shell with only the dependencies needed to run the bazel steps.
            bazelShell = with pkgs; mkShell {
              shellHook = ''
                export ANDROID_HOME="${androidSdk}/libexec/android-sdk"
                export GRADLE_OPTS="-Dorg.gradle.project.android.aapt2FromMavenOverride=${androidSdk}/libexec/android-sdk/build-tools/28.0.3/aapt2";
                export FOO="${fff}"
              '';
              packages = [
                jdk11_headless
                bazel_7
                androidSdk
                bazel-buildtools
              ];
            };
            # Shell for building Oak Containers kernel and system image. This is not included in the
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
                elfutils
                flex
                jq
                libelf
                perl
                glibc
                glibc.static
                ncurses
                netcat
                umoci
              ];
            };
            # Shell for container kernel image provenance workflow.
            bzImageProvenance = with pkgs; mkShell {
              inputsFrom = [
                rust
              ];
              packages = [
                bc
                bison
                curl
                elfutils
                flex
                libelf
              ];
            };
            # Shell for container stage 1 image provenance workflow.
            stage1Provenance = with pkgs; mkShell {
              inputsFrom = [
                rust
              ];
              packages = [
                cpio
                glibc
                glibc.static
              ];
            };
            # Shell for most CI steps (i.e. without contaniners support).
            ci = pkgs.mkShell {
              inputsFrom = [
                rust
                bazelShell
                lint
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
