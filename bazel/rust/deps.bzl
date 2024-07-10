"""Helpers to load rust-related repositories."""

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def load_rust_repositories():
    http_archive(
        name = "rules_rust",
        sha256 = "59e7afd6ecf6433b4194303cf095fa03537bd92b9c0f557c941b1a9623344d38",
        urls = ["https://github.com/bazelbuild/rules_rust/releases/download/0.48.0/rules_rust-v0.48.0.tar.gz"],
    )
