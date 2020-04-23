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
  "notice", # "MIT,Apache-2.0"
])

load(
    "@io_bazel_rules_rust//rust:rust.bzl",
    "rust_library",
    "rust_binary",
    "rust_test",
)


# Unsupported target "badssl" with type "test" omitted
# Unsupported target "early-data" with type "test" omitted
# Unsupported target "test" with type "test" omitted

rust_library(
    name = "tokio_rustls",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__futures_core__0_3_4//:futures_core",
        "@raze__rustls__0_16_0//:rustls",
        "@raze__tokio__0_2_19//:tokio",
        "@raze__webpki__0_21_2//:webpki",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.12.2",
    crate_features = [
    ],
)

