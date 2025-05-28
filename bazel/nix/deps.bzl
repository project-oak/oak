"""Load nixpkgs repos"""

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def load_nixpkgs_repositories():
    http_archive(
        name = "io_tweag_rules_nixpkgs",
        strip_prefix = "rules_nixpkgs-0.13.0",
        urls = ["https://github.com/tweag/rules_nixpkgs/archive/refs/tags/v0.13.0.tar.gz"],
    )
