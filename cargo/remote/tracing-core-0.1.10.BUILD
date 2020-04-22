"""
cargo-raze crate build file.

DO NOT EDIT! Replaced on runs of cargo-raze
"""
package(default_visibility = [
  # Public for visibility by "@raze__crate__version//" targets.
  #
  # Prefer access through "//cargo", which limits external
  # visibility to explicit Cargo.toml dependencies.
  "//visibility:public",
])

licenses([
  "notice", # "MIT"
])

load(
    "@io_bazel_rules_rust//rust:rust.bzl",
    "rust_library",
    "rust_binary",
    "rust_test",
)


# Unsupported target "dispatch" with type "test" omitted
# Unsupported target "global_dispatch" with type "test" omitted
# Unsupported target "macros" with type "test" omitted

rust_library(
    name = "tracing_core",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__lazy_static__1_4_0//:lazy_static",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.1.10",
    crate_features = [
        "lazy_static",
        "std",
    ],
)

