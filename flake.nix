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
          # Create a bazelisk package that can be called as "bazel".
          bazelisk-as-bazel = pkgs.symlinkJoin {
            name = "bazelisk-as-bazel";
            paths = [ pkgs.bazelisk ];
            postBuild = ''
              # Remove the original binary link if you only want the alias
              # or keep it. Here we explicitly create the alias link:
              ln -s $out/bin/bazelisk $out/bin/bazel
            '';
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
                fd
                gettext
                google-cloud-sdk
                just
                ps
                which
              ]
              ++
              # Linux-specific dependencies.
              lib.optionals stdenv.isLinux [
                kmod
              ];
            };
            # Minimal shell with only the dependencies needed to run the Rust tests.
            rust = with pkgs; mkShell {
              # iconv is needed for the Rust toolchain to work correctly on macOS.
              # See b/427475113 for more details.
              # Here we expose an environment variable to allow checking the exact path of the
              # iconv library, to be used when updating the absolute path in .bazelrc.
              shellHook = ''
                export ICONV_PATH="${iconv}"
              '';
              inputsFrom = [
                base
              ];
              packages = [
                (rust-bin.selectLatestNightlyWith (toolchain: rustToolchain))
                cargo-audit
                protobuf
                buf # utility to convert binary protobuf to json; for breaking change detection.
                qemu_kvm
                python312
                wasm-pack
                iconv
                util-linux
              ]
              ++
              # Linux-specific dependencies.
              lib.optionals stdenv.isLinux [
                iproute2
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
                shfmt
                pre-commit
              ];
            };
            # Minimal shell with only the dependencies needed to run the bazel steps.
            bazelShell = with pkgs; mkShell {
              shellHook = ''
                export ANDROID_HOME="${androidSdk}/libexec/android-sdk"
                export GRADLE_OPTS="-Dorg.gradle.project.android.aapt2FromMavenOverride=${androidSdk}/libexec/android-sdk/build-tools/28.0.3/aapt2"
                export PKG_CONFIG_PATH="${pkgs.openssl.dev}/lib/pkgconfig"

                # Prevent issues when trying to do nix builds inside of a nix shell.
                # https://github.com/NixOS/nix/issues/262
                unset TMPDIR

                export BAZELISK_VERIFY_SHA256=${if stdenv.isDarwin then "cb6d2f19ad92157e7186f64151e665c1b0c3bacaa690784e66f446f1b7660140" else "61d89402f0368e64b6c827be5de79d8e65382e8124c3cbb97325611a1851392e"}
              '';
              packages = [
                autoconf
                autogen
                automake
                jdk17_headless
                bazelisk-as-bazel
                androidSdk
                bazel-buildtools
                openssl
                pkg-config
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
                cosign
                curlWithGnuTls
                docker
                fakeroot
                flex
                gcrane
                jq
                libelf
                perl
                rekor-cli
                strip-nondeterminism
                ncurses
                netcat
                umoci
              ]
              ++
              # Linux-specific dependencies.
              lib.optionals stdenv.isLinux [
                datefudge
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
              # Attempt to install a module needed locally for development if it's not already.
              shellHook = ''
                modprobe vhost_vsock || cat << EOF

                NOTE:

                Failed to install vhost_vsock module, some integration tests may not work.
                To resolve this, you can try running:

                sudo modprobe vhost_vsock

                EOF
              '';
              packages = [
                pkgs.terraform
              ];
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
