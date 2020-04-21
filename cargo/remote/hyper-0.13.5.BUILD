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


# Unsupported target "body" with type "bench" omitted
# Unsupported target "client" with type "example" omitted
# Unsupported target "client" with type "test" omitted
# Unsupported target "client_json" with type "example" omitted
# Unsupported target "connect" with type "bench" omitted
# Unsupported target "echo" with type "example" omitted
# Unsupported target "end_to_end" with type "bench" omitted
# Unsupported target "gateway" with type "example" omitted
# Unsupported target "hello" with type "example" omitted
# Unsupported target "http_proxy" with type "example" omitted

rust_library(
    name = "hyper",
    crate_root = "src/lib.rs",
    crate_type = "lib",
    edition = "2018",
    srcs = glob(["**/*.rs"]),
    deps = [
        "@raze__bytes__0_5_4//:bytes",
        "@raze__futures_channel__0_3_4//:futures_channel",
        "@raze__futures_core__0_3_4//:futures_core",
        "@raze__futures_util__0_3_4//:futures_util",
        "@raze__h2__0_2_4//:h2",
        "@raze__http__0_2_1//:http",
        "@raze__http_body__0_3_1//:http_body",
        "@raze__httparse__1_3_4//:httparse",
        "@raze__itoa__0_4_5//:itoa",
        "@raze__log__0_4_8//:log",
        "@raze__net2__0_2_33//:net2",
        "@raze__pin_project__0_4_9//:pin_project",
        "@raze__time__0_1_42//:time",
        "@raze__tokio__0_2_18//:tokio",
        "@raze__tower_service__0_3_0//:tower_service",
        "@raze__want__0_3_0//:want",
    ],
    rustc_flags = [
        "--cap-lints=allow",
    ],
    version = "0.13.5",
    crate_features = [
        "default",
        "net2",
        "runtime",
        "stream",
        "tcp",
    ],
)

# Unsupported target "integration" with type "test" omitted
# Unsupported target "multi_server" with type "example" omitted
# Unsupported target "params" with type "example" omitted
# Unsupported target "pipeline" with type "bench" omitted
# Unsupported target "send_file" with type "example" omitted
# Unsupported target "server" with type "bench" omitted
# Unsupported target "server" with type "test" omitted
# Unsupported target "single_threaded" with type "example" omitted
# Unsupported target "state" with type "example" omitted
# Unsupported target "tower_client" with type "example" omitted
# Unsupported target "tower_server" with type "example" omitted
# Unsupported target "upgrades" with type "example" omitted
# Unsupported target "web_api" with type "example" omitted
