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


# Unsupported target "codecs" with type "test" omitted
# Unsupported target "framed" with type "test" omitted
# Unsupported target "framed_read" with type "test" omitted
# Unsupported target "framed_write" with type "test" omitted
# Unsupported target "length_delimited" with type "test" omitted

rust_library(
    name = "tokio_util",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__bytes__0_5_4//:bytes",
        "@raze__futures_core__0_3_5//:futures_core",
        "@raze__futures_sink__0_3_5//:futures_sink",
        "@raze__log__0_4_8//:log",
        "@raze__pin_project_lite__0_1_4//:pin_project_lite",
        "@raze__tokio__0_2_19//:tokio",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.3.1",
    crate_features = [
        "codec",
        "default",
    ],
)

# Unsupported target "udp" with type "test" omitted
