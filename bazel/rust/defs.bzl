"""Functions to set up the various rust-related dependencies."""

load("@rules_rust//rust:repositories.bzl", "rules_rust_dependencies", "rust_register_toolchains", "rust_repository_set")
load("@rules_rust//tools/rust_analyzer:deps.bzl", "rust_analyzer_dependencies")

RUST_NIGHTLY_DATE = "2024-02-01"

RUST_NIGHTLY_VERSION = "nightly/" + RUST_NIGHTLY_DATE

RUST_VERSIONS = [
    "1.76.0",
    RUST_NIGHTLY_VERSION,
]

RUST_EDITION = "2021"

def setup_rust_dependencies():
    """Set up the various rust-related dependencies. Call this after load_rust_repositories()."""
    rules_rust_dependencies()

    rust_register_toolchains(
        edition = RUST_EDITION,
        versions = RUST_VERSIONS,
        sha256s = {
            RUST_NIGHTLY_DATE + "/rustc-nightly-x86_64-unknown-linux-gnu.tar.xz": "7247ca497c7d9194c9e7bb9b6a51f8ccddc452bbce2977d608cabdbc1a0f332f",
            RUST_NIGHTLY_DATE + "/clippy-nightly-x86_64-unknown-linux-gnu.tar.xz": "1271eaa89d50bd7f63b338616c36f41fe1e733b5d6c4cc2c95eaa6b3c8faba62",
            RUST_NIGHTLY_DATE + "/cargo-nightly-x86_64-unknown-linux-gnu.tar.xz": "1d859549b5f3d2dd146b84aa13dfec24a05913653af2116b39a919cab69de850",
            RUST_NIGHTLY_DATE + "/llvm-tools-nightly-x86_64-unknown-linux-gnu.tar.xz": "b227753189981d9a115527ba0e95b365388fb0fe7f1a1ff93116c4448c854197",
            RUST_NIGHTLY_DATE + "/rust-std-nightly-x86_64-unknown-linux-gnu.tar.xz": "b1a444f8e8f33d813c4d532c12717743edd9b34f685ff5293b6375fc75c2421e",
        },
    )

    _BARE_METAL_RUSTC_FLAGS = [
        "-C",
        "target-feature=+avx,+avx2,-soft-float",
    ]

    # Creates remote repositories for Rust toolchains, required for cross-compiling.
    rust_repository_set(
        name = "rust_toolchain_repo",
        edition = RUST_EDITION,
        exec_triple = "x86_64-unknown-linux-gnu",
        extra_rustc_flags = {
            "x86_64-unknown-none": _BARE_METAL_RUSTC_FLAGS,
        },
        extra_target_triples = {
            "x86_64-unknown-none": [
                "@platforms//cpu:x86_64",
                "@platforms//os:none",
            ],
        },
        versions = RUST_VERSIONS,
    )

    # IDE support via rust-analyzer for bazel-only projects.
    # https://bazelbuild.github.io/rules_rust/rust_analyzer.html
    #
    # You can re-generate the rust-project.json file using:
    # bazel run @rules_rust//tools/rust_analyzer:gen_rust_project
    #
    # It should not be committed.
    #
    # VSCode users: There's a task included in .vscode/tasks.json that should
    # automatically do this for you when needed.
    rust_analyzer_dependencies()
