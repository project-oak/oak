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


# Unsupported target "init" with type "example" omitted
# Unsupported target "init_with_level" with type "example" omitted

rust_library(
    name = "simple_logger",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2015",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__chrono__0_4_11//:chrono",
        "@raze__colored__1_9_3//:colored",
        "@raze__log__0_4_8//:log",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "1.6.0",
    crate_features = [
        "chrono",
        "colored",
        "default",
    ],
)

