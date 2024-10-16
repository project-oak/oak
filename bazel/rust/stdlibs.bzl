"""Helpers to download the rust std lib source and build it to make it available to a rust toolchain."""

load("//bazel/rust:defs.bzl", "RUST_NIGHTLY_DATE", "STDLIBS_SHA256")

def _stdlibs_impl(repository_ctx):
    repository_ctx.download_and_extract(
        url = "https://static.rust-lang.org/dist/" + repository_ctx.attr.nightly_date + "/rustc-nightly-src.tar.gz",
        type = "tar.gz",
        sha256 = repository_ctx.attr.sha256,
        stripPrefix = "rustc-nightly-src",
    )

    repository_ctx.file(
        "BUILD",
        content = repository_ctx.read(repository_ctx.attr.build_file),
    )

stdlibs = repository_rule(
    implementation = _stdlibs_impl,
    attrs = {
        "nightly_date": attr.string(mandatory = True, doc = "The date of the nightly rust std libs to download."),
        "sha256": attr.string(mandatory = False, doc = "The expected SHA2-256 digest of the nightly rust std libs archive."),
        "build_file": attr.label(mandatory = True, doc = "The BUILD file to use for building the rust std libs."),
    },
)

def setup_rebuilt_rust_stdlibs(name = "unused"):
    # Download rust std library sources to enable rebuilding.
    stdlibs(
        name = "stdlibs",
        build_file = "//bazel/rust:stdlibs.BUILD",
        nightly_date = RUST_NIGHTLY_DATE,
        sha256 = STDLIBS_SHA256,
    )

    # Register a toolchain using the rebuilt std libraries.
    native.register_toolchains(
        "//bazel/rust/rebuilt_toolchain:toolchain_rebuilt_x86_64-unknown-none",
    )
