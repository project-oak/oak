"""Helpers to load rust-related repositories."""

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def load_rust_repositories():
    http_archive(
        name = "rules_rust",
        sha256 = "17c53bf800b932f32d3ca19d2cb9e8ad533ce1c0d729f0d183077bfddab7ad46",
        urls = ["https://github.com/bazelbuild/rules_rust/releases/download/0.46.0/rules_rust-v0.46.0.tar.gz"],
    )
