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
  "notice", # "Apache-2.0,MIT"
])

load(
    "@io_bazel_rules_rust//rust:rust.bzl",
    "rust_library",
    "rust_binary",
    "rust_test",
)


# Unsupported target "bench" with type "bench" omitted
# Unsupported target "equivalent_trait" with type "test" omitted
# Unsupported target "faststring" with type "bench" omitted

rust_library(
    name = "indexmap",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2015",
    srcs = glob(["**/*.rs"]),
    deps = [
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "1.0.2",
    crate_features = [
    ],
)

# Unsupported target "quick" with type "test" omitted
# Unsupported target "serde" with type "test" omitted
# Unsupported target "tests" with type "test" omitted
