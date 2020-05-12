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


# Unsupported target "bench" with type "example" omitted
# Unsupported target "bench_acquire" with type "example" omitted
# Unsupported target "bench_vs_lazy_static" with type "example" omitted
# Unsupported target "lazy_static" with type "example" omitted

rust_library(
    name = "once_cell",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "1.3.1",
    crate_features = [
        "std",
    ],
)

# Unsupported target "reentrant_init_deadlocks" with type "example" omitted
# Unsupported target "regex" with type "example" omitted
# Unsupported target "test" with type "test" omitted
# Unsupported target "test_synchronization" with type "example" omitted
