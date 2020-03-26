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


# Unsupported target "akamai" with type "example" omitted
# Unsupported target "client" with type "example" omitted

rust_library(
    name = "h2",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__bytes__0_5_4//:bytes",
        "@raze__fnv__1_0_6//:fnv",
        "@raze__futures_core__0_3_4//:futures_core",
        "@raze__futures_sink__0_3_4//:futures_sink",
        "@raze__futures_util__0_3_4//:futures_util",
        "@raze__http__0_2_1//:http",
        "@raze__indexmap__1_0_2//:indexmap",
        "@raze__log__0_4_8//:log",
        "@raze__slab__0_4_2//:slab",
        "@raze__tokio__0_2_18//:tokio",
        "@raze__tokio_util__0_3_1//:tokio_util",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.2.4",
    crate_features = [
    ],
)

# Unsupported target "server" with type "example" omitted
