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
  "restricted", # "no license"
])

load(
    "@io_bazel_rules_rust//rust:rust.bzl",
    "rust_library",
    "rust_binary",
    "rust_test",
)


# Unsupported target "dns_name_tests" with type "test" omitted
# Unsupported target "integration" with type "test" omitted

rust_library(
    name = "webpki",
    crate_root = "src/webpki.rs",
    crate_type = "lib",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__ring__0_16_12//:ring",
        "@raze__untrusted__0_7_0//:untrusted",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    data = glob(["**/*.der"]),
    version = "0.21.2",
    crate_features = [
        "default",
        "std",
        "trust_anchor_util",
    ],
)

