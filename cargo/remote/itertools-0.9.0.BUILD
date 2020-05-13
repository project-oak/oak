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


# Unsupported target "adaptors_no_collect" with type "test" omitted
# Unsupported target "bench1" with type "bench" omitted
# Unsupported target "combinations_with_replacement" with type "bench" omitted
# Unsupported target "fold_specialization" with type "bench" omitted
# Unsupported target "fold_specialization" with type "test" omitted
# Unsupported target "iris" with type "example" omitted

rust_library(
    name = "itertools",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__either__1_5_3//:either",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.9.0",
    crate_features = [
        "default",
        "use_std",
    ],
)

# Unsupported target "merge_join" with type "test" omitted
# Unsupported target "peeking_take_while" with type "test" omitted
# Unsupported target "quick" with type "test" omitted
# Unsupported target "specializations" with type "test" omitted
# Unsupported target "test_core" with type "test" omitted
# Unsupported target "test_std" with type "test" omitted
# Unsupported target "tree_fold1" with type "bench" omitted
# Unsupported target "tuple_combinations" with type "bench" omitted
# Unsupported target "tuples" with type "bench" omitted
# Unsupported target "tuples" with type "test" omitted
# Unsupported target "zip" with type "test" omitted
