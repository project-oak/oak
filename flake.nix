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
    crane.inputs.rust-overlay.follows = "rust-overlay";
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
            pkgs.rust-bin.nightly.latest.default.override {
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
              packages = [
                just
                ps
                which
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
                qemu_kvm
                python312
              ];
            };
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
                nodePackages.prettier
                nodePackages.prettier-plugin-toml
                shellcheck
              ];
              shellHook = ''
                export NODE_PATH=${nodePackages.prettier-plugin-toml}/lib/node_modules:$NODE_PATH
              '';
            };
            # Minimal shell with only the dependencies needed to run the bazel steps.
            bazelShell = with pkgs; mkShell {
              shellHook = ''
                export ANDROID_HOME="${androidSdk}/libexec/android-sdk"
                export GRADLE_OPTS="-Dorg.gradle.project.android.aapt2FromMavenOverride=${androidSdk}/libexec/android-sdk/build-tools/28.0.3/aapt2";
              '';
              packages = [
                jdk11_headless
                bazel
                androidSdk
                bazel-buildtools
              ];
            };
            # Shell for building Oak Containers kernel and system image. This is not included in the 
            # default shell because it is not needed as part of the CI.
            containers = with pkgs; mkShell {
              inputsFrom = [
                base
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
                runc
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