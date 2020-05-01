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


# Unsupported target "cleanup" with type "test" omitted
# Unsupported target "cleanup_indirect" with type "test" omitted
# Unsupported target "default" with type "test" omitted
# Unsupported target "iterator" with type "test" omitted

rust_library(
    name = "signal_hook",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2015",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__libc__0_2_69//:libc",
        "@raze__signal_hook_registry__1_2_0//:signal_hook_registry",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.1.13",
    crate_features = [
    ],
)

# Unsupported target "tokio" with type "test" omitted
# Unsupported target "version" with type "test" omitted
