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


# Unsupported target "event" with type "test" omitted
# Unsupported target "filter_caching_is_lexically_scoped" with type "test" omitted
# Unsupported target "filters_are_not_reevaluated_for_the_same_span" with type "test" omitted
# Unsupported target "filters_are_reevaluated_for_different_call_sites" with type "test" omitted
# Unsupported target "macro_imports" with type "test" omitted
# Unsupported target "macros" with type "test" omitted
# Unsupported target "no_subscriber" with type "bench" omitted
# Unsupported target "span" with type "test" omitted
# Unsupported target "subscriber" with type "bench" omitted
# Unsupported target "subscriber" with type "test" omitted

rust_library(
    name = "tracing",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__cfg_if__0_1_10//:cfg_if",
        "@raze__log__0_4_8//:log",
        "@raze__tracing_attributes__0_1_7//:tracing_attributes",
        "@raze__tracing_core__0_1_10//:tracing_core",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.1.13",
    crate_features = [
        "attributes",
        "default",
        "log",
        "std",
        "tracing-attributes",
    ],
)

