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


rust_binary(
    # Prefix bin name to disambiguate from (probable) collision with lib name
    # N.B.: The exact form of this is subject to change.
    name = "cargo_bin_instantiate",
    crate_root = "src/bin/instantiate.rs",
    edition = "2015",
    srcs = glob(["**/*.rs"]),
    deps = [
        # Binaries get an implicit dependency on their crate's lib
        ":wasmi",
        "@raze__libc__0_2_69//:libc",
        "@raze__libm__0_1_4//:libm",
        "@raze__memory_units__0_3_0//:memory_units",
        "@raze__num_rational__0_2_4//:num_rational",
        "@raze__num_traits__0_2_11//:num_traits",
        "@raze__parity_wasm__0_41_0//:parity_wasm",
        "@raze__wasmi_validation__0_3_0//:wasmi_validation",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.6.2",
    crate_features = [
        "core",
        "libm",
        "vec_memory",
    ],
)

# Unsupported target "interpret" with type "example" omitted
# Unsupported target "invoke" with type "example" omitted
# Unsupported target "tictactoe" with type "example" omitted

rust_library(
    name = "wasmi",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2015",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__libc__0_2_69//:libc",
        "@raze__libm__0_1_4//:libm",
        "@raze__memory_units__0_3_0//:memory_units",
        "@raze__num_rational__0_2_4//:num_rational",
        "@raze__num_traits__0_2_11//:num_traits",
        "@raze__parity_wasm__0_41_0//:parity_wasm",
        "@raze__wasmi_validation__0_3_0//:wasmi_validation",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.6.2",
    crate_features = [
        "core",
        "libm",
        "vec_memory",
    ],
)

