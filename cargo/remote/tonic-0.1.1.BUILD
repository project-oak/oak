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


# Unsupported target "decode" with type "bench" omitted

rust_library(
    name = "tonic",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__async_stream__0_2_1//:async_stream",
        "@raze__async_trait__0_1_30//:async_trait",
        "@raze__base64__0_10_1//:base64",
        "@raze__bytes__0_5_4//:bytes",
        "@raze__futures_core__0_3_4//:futures_core",
        "@raze__futures_util__0_3_4//:futures_util",
        "@raze__http__0_2_1//:http",
        "@raze__http_body__0_3_1//:http_body",
        "@raze__hyper__0_13_5//:hyper",
        "@raze__percent_encoding__1_0_1//:percent_encoding",
        "@raze__pin_project__0_4_9//:pin_project",
        "@raze__prost__0_6_1//:prost",
        "@raze__prost_derive__0_6_1//:prost_derive",
        "@raze__tokio__0_2_19//:tokio",
        "@raze__tokio_rustls__0_12_2//:tokio_rustls",
        "@raze__tokio_util__0_2_0//:tokio_util",
        "@raze__tower__0_3_1//:tower",
        "@raze__tower_balance__0_3_0//:tower_balance",
        "@raze__tower_load__0_3_0//:tower_load",
        "@raze__tower_make__0_3_0//:tower_make",
        "@raze__tower_service__0_3_0//:tower_service",
        "@raze__tracing__0_1_13//:tracing",
        "@raze__tracing_futures__0_2_4//:tracing_futures",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.1.1",
    crate_features = [
        "async-trait",
        "codegen",
        "default",
        "hyper",
        "prost",
        "prost-derive",
        "tls",
        "tokio",
        "tokio-rustls",
        "tower",
        "tower-balance",
        "tower-load",
        "tracing-futures",
        "transport",
    ],
)

