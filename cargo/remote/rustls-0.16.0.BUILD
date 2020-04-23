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
  "notice", # "Apache-2.0,ISC,MIT"
])

load(
    "@io_bazel_rules_rust//rust:rust.bzl",
    "rust_library",
    "rust_binary",
    "rust_test",
)


# Unsupported target "api" with type "test" omitted
# Unsupported target "bench" with type "example" omitted
# Unsupported target "benchmarks" with type "bench" omitted
# Unsupported target "benchmarks" with type "test" omitted
# Unsupported target "bogo_shim" with type "example" omitted

rust_library(
    name = "rustls",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__base64__0_10_1//:base64",
        "@raze__log__0_4_8//:log",
        "@raze__ring__0_16_12//:ring",
        "@raze__sct__0_6_0//:sct",
        "@raze__webpki__0_21_2//:webpki",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.16.0",
    crate_features = [
        "default",
        "log",
        "logging",
    ],
)

# Unsupported target "trytls_shim" with type "example" omitted
