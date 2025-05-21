"""Helpers to load rust-related repositories."""

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def load_rust_repositories():
    http_archive(
        name = "platforms",
        urls = [
            "https://mirror.bazel.build/github.com/bazelbuild/platforms/releases/download/0.0.11/platforms-0.0.11.tar.gz",
            "https://github.com/bazelbuild/platforms/releases/download/0.0.11/platforms-0.0.11.tar.gz",
        ],
        sha256 = "29742e87275809b5e598dc2f04d86960cc7a55b3067d97221c9abbc9926bff0f",
    )
    http_archive(
        name = "rules_rust",
        integrity = "sha256-U8G6x+xI985IxMHGqgBvJ1Fa3SrrBXJZNyJObgDsfOo=",
        urls = ["https://github.com/bazelbuild/rules_rust/releases/download/0.61.0/rules_rust-0.61.0.tar.gz"],
    )
