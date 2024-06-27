"""Functions to set up the various rust-related dependencies."""

load("@rules_rust//rust:repositories.bzl", "rules_rust_dependencies", "rust_register_toolchains", "rust_repository_set")
load("@rules_rust//tools/rust_analyzer:deps.bzl", "rust_analyzer_dependencies")
load("//bazel:defs.bzl", "RUST_EDITION", "RUST_VERSIONS")

def setup_rust_dependencies():
    """Set up the various rust-related dependencies. Call this after load_rust_repositories()."""
    rules_rust_dependencies()

    rust_register_toolchains(
        edition = RUST_EDITION,
        versions = RUST_VERSIONS,
    )

    _BARE_METAL_RUSTC_FLAGS = [
        "-C",
        "relocation-model=static",
        "-C",
        "target-feature=+sse,+sse2,+ssse3,+sse4.1,+sse4.2,+avx,+avx2,+rdrand,-soft-float",
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
