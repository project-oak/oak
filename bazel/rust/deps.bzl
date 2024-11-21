"""Helpers to load rust-related repositories."""

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def load_rust_repositories():
    http_archive(
        name = "rules_rust",
        sha256 = "af4f56caae50a99a68bfce39b141b509dd68548c8204b98ab7a1cafc94d5bb02",
        urls = ["https://github.com/bazelbuild/rules_rust/releases/download/0.54.1/rules_rust-v0.54.1.tar.gz"],
    )
