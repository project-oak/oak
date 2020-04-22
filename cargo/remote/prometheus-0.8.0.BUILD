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
  "notice", # "Apache-2.0"
])

load(
    "@io_bazel_rules_rust//rust:rust.bzl",
    "rust_library",
    "rust_binary",
    "rust_test",
)


# Unsupported target "atomic" with type "bench" omitted
# Unsupported target "build-script-build" with type "custom-build" omitted
# Unsupported target "counter" with type "bench" omitted
# Unsupported target "example_custom_registry" with type "example" omitted
# Unsupported target "example_edition_2018" with type "example" omitted
# Unsupported target "example_embed" with type "example" omitted
# Unsupported target "example_hyper" with type "example" omitted
# Unsupported target "example_int_metrics" with type "example" omitted
# Unsupported target "example_process_collector" with type "example" omitted
# Unsupported target "example_push" with type "example" omitted
# Unsupported target "gauge" with type "bench" omitted
# Unsupported target "histogram" with type "bench" omitted

rust_library(
    name = "prometheus",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__cfg_if__0_1_10//:cfg_if",
        "@raze__fnv__1_0_6//:fnv",
        "@raze__lazy_static__1_4_0//:lazy_static",
        "@raze__libc__0_2_69//:libc",
        "@raze__spin__0_5_2//:spin",
        "@raze__thiserror__1_0_15//:thiserror",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.8.0",
    crate_features = [
        "libc",
        "nightly",
    ],
)

