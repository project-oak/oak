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


# Unsupported target "demo" with type "example" omitted

rust_library(
    name = "tower_balance",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__futures_core__0_3_5//:futures_core",
        "@raze__futures_util__0_3_5//:futures_util",
        "@raze__indexmap__1_0_2//:indexmap",
        "@raze__pin_project__0_4_9//:pin_project",
        "@raze__rand__0_7_3//:rand",
        "@raze__slab__0_4_2//:slab",
        "@raze__tokio__0_2_19//:tokio",
        "@raze__tower_discover__0_3_0//:tower_discover",
        "@raze__tower_layer__0_3_0//:tower_layer",
        "@raze__tower_load__0_3_0//:tower_load",
        "@raze__tower_make__0_3_0//:tower_make",
        "@raze__tower_ready_cache__0_3_1//:tower_ready_cache",
        "@raze__tower_service__0_3_0//:tower_service",
        "@raze__tracing__0_1_13//:tracing",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.3.0",
    crate_features = [
        "default",
        "log",
    ],
)

