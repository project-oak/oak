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


# Unsupported target "ahash" with type "bench" omitted

rust_library(
    name = "ahash",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__const_random__0_1_8//:const_random",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.3.2",
    crate_features = [
        "compile-time-rng",
        "const-random",
    ],
)

# Unsupported target "bench" with type "test" omitted
# Unsupported target "map" with type "bench" omitted
# Unsupported target "map_tests" with type "test" omitted
# Unsupported target "nopanic" with type "test" omitted
