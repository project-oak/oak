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


# Unsupported target "channel" with type "test" omitted

rust_library(
    name = "futures_channel",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__futures_core__0_3_5//:futures_core",
        "@raze__futures_sink__0_3_5//:futures_sink",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.3.5",
    crate_features = [
        "alloc",
        "default",
        "futures-sink",
        "sink",
        "std",
    ],
)

# Unsupported target "mpsc" with type "test" omitted
# Unsupported target "mpsc-close" with type "test" omitted
# Unsupported target "oneshot" with type "test" omitted
# Unsupported target "sync_mpsc" with type "bench" omitted
