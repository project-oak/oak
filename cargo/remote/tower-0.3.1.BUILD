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


# Unsupported target "builder" with type "test" omitted

rust_library(
    name = "tower",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__futures_core__0_3_4//:futures_core",
        "@raze__tower_buffer__0_3_0//:tower_buffer",
        "@raze__tower_discover__0_3_0//:tower_discover",
        "@raze__tower_layer__0_3_0//:tower_layer",
        "@raze__tower_limit__0_3_1//:tower_limit",
        "@raze__tower_load_shed__0_3_0//:tower_load_shed",
        "@raze__tower_retry__0_3_0//:tower_retry",
        "@raze__tower_service__0_3_0//:tower_service",
        "@raze__tower_timeout__0_3_0//:tower_timeout",
        "@raze__tower_util__0_3_1//:tower_util",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.3.1",
    crate_features = [
        "default",
        "full",
        "log",
    ],
)

