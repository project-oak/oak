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


# Unsupported target "bench-decoder" with type "example" omitted
# Unsupported target "build" with type "example" omitted
# Unsupported target "data" with type "example" omitted
# Unsupported target "exports" with type "example" omitted
# Unsupported target "info" with type "example" omitted
# Unsupported target "inject" with type "example" omitted

rust_library(
    name = "parity_wasm",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.41.0",
    crate_features = [
    ],
)

# Unsupported target "roundtrip" with type "example" omitted
# Unsupported target "show" with type "example" omitted
