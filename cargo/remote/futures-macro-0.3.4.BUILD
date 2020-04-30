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
    name = "futures_macro",
    crate_root = "src/lib.rs",
    crate_type = "proc-macro",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__proc_macro_hack__0_5_15//:proc_macro_hack",
        "@raze__proc_macro2__1_0_10//:proc_macro2",
        "@raze__quote__1_0_3//:quote",
        "@raze__syn__1_0_18//:syn",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.3.4",
    crate_features = [
    ],
)

