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



rust_library(
    name = "async_stream",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__async_stream_impl__0_2_1//:async_stream_impl",
        "@raze__futures_core__0_3_5//:futures_core",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.2.1",
    crate_features = [
    ],
)

# Unsupported target "for_await" with type "test" omitted
# Unsupported target "stream" with type "test" omitted
# Unsupported target "tcp_accept" with type "example" omitted
# Unsupported target "try_stream" with type "test" omitted
