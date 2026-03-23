load("@rules_rust//rust:defs.bzl", "rust_binary")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_binary(
    name = "analysis",
    srcs = ["main.rs"],
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        "//database:oak_private_memory_database",
        "//proto:sealed_memory_rust_proto",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:log",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:rand",
    ],
)

rust_binary(
    name = "icing_benchmark",
    srcs = ["icing_benchmark.rs"],
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        "//database:oak_private_memory_database",
        "//proto:sealed_memory_rust_proto",
        "//src/icing",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:log",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:rand",
    ],
)

rust_binary(
    name = "index_preservation_benchmark",
    srcs = ["index_preservation_benchmark.rs"],
    deps = [
        "//database:oak_private_memory_database",
        "//proto:sealed_memory_rust_proto",
        "//src/icing",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:log",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:rand",
    ],
)
