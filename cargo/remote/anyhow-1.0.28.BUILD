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



rust_library(
    name = "anyhow",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "1.0.28",
    crate_features = [
        "default",
        "std",
    ],
)

# Unsupported target "build-script-build" with type "custom-build" omitted
# Unsupported target "compiletest" with type "test" omitted
# Unsupported target "test_autotrait" with type "test" omitted
# Unsupported target "test_backtrace" with type "test" omitted
# Unsupported target "test_boxed" with type "test" omitted
# Unsupported target "test_chain" with type "test" omitted
# Unsupported target "test_context" with type "test" omitted
# Unsupported target "test_convert" with type "test" omitted
# Unsupported target "test_downcast" with type "test" omitted
# Unsupported target "test_fmt" with type "test" omitted
# Unsupported target "test_macros" with type "test" omitted
# Unsupported target "test_repr" with type "test" omitted
# Unsupported target "test_source" with type "test" omitted
