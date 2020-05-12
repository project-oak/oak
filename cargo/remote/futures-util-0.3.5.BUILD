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
  "restricted", # "MIT OR Apache-2.0"
])

load(
    "@io_bazel_rules_rust//rust:rust.bzl",
    "rust_library",
    "rust_binary",
    "rust_test",
)



rust_library(
    name = "futures_util",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__futures_channel__0_3_5//:futures_channel",
        "@raze__futures_core__0_3_5//:futures_core",
        "@raze__futures_io__0_3_5//:futures_io",
        "@raze__futures_macro__0_3_5//:futures_macro",
        "@raze__futures_sink__0_3_5//:futures_sink",
        "@raze__futures_task__0_3_5//:futures_task",
        "@raze__memchr__2_3_3//:memchr",
        "@raze__pin_project__0_4_9//:pin_project",
        "@raze__pin_utils__0_1_0//:pin_utils",
        "@raze__proc_macro_hack__0_5_15//:proc_macro_hack",
        "@raze__proc_macro_nested__0_1_4//:proc_macro_nested",
        "@raze__slab__0_4_2//:slab",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.3.5",
    crate_features = [
        "alloc",
        "async-await",
        "async-await-macro",
        "channel",
        "futures-channel",
        "futures-io",
        "futures-macro",
        "futures-sink",
        "io",
        "memchr",
        "proc-macro-hack",
        "proc-macro-nested",
        "sink",
        "slab",
        "std",
    ],
)

# Unsupported target "futures_unordered" with type "bench" omitted
