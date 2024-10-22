load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_containers_channel",
    srcs = [
        "src/lib.rs",
    ],
    deps = [
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:tokio-vsock",
        "@oak_crates_index//:tonic",
        "@oak_crates_index//:tower",
    ],
)

rust_test(
    name = "channel_test",
    crate = ":channel",
    deps = [
        "//oak_proto_rust",
        "//oak_proto_rust/grpc",
        "@oak_crates_index//:async-stream",
        "@oak_crates_index//:futures",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
    ],
)

alias(
    name = "channel",
    actual = ":oak_containers_channel",
)
