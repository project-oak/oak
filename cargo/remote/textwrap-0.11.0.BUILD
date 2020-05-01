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


# Unsupported target "layout" with type "example" omitted
# Unsupported target "linear" with type "bench" omitted
# Unsupported target "termwidth" with type "example" omitted

rust_library(
    name = "textwrap",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2015",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__unicode_width__0_1_7//:unicode_width",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.11.0",
    crate_features = [
    ],
)

# Unsupported target "version-numbers" with type "test" omitted
