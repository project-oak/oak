load("@rules_rust//rust:defs.bzl", "rust_binary")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_binary(
    name = "analysis",
    srcs = ["main.rs"],
    deps = [
        "//database:oak_private_memory_database",
        "//proto:sealed_memory_rust_proto",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:rand",
    ],
)
