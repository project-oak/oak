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


# Unsupported target "buf" with type "bench" omitted
# Unsupported target "bytes" with type "bench" omitted

rust_library(
    name = "bytes",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.5.4",
    crate_features = [
        "default",
        "std",
    ],
)

# Unsupported target "bytes_mut" with type "bench" omitted
# Unsupported target "test_buf" with type "test" omitted
# Unsupported target "test_buf_mut" with type "test" omitted
# Unsupported target "test_bytes" with type "test" omitted
# Unsupported target "test_bytes_odd_alloc" with type "test" omitted
# Unsupported target "test_bytes_vec_alloc" with type "test" omitted
# Unsupported target "test_chain" with type "test" omitted
# Unsupported target "test_debug" with type "test" omitted
# Unsupported target "test_iter" with type "test" omitted
# Unsupported target "test_reader" with type "test" omitted
# Unsupported target "test_serde" with type "test" omitted
# Unsupported target "test_take" with type "test" omitted
