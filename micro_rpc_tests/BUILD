load("@rules_rust//rust:defs.bzl", "rust_test")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_test(
    name = "test_schema",
    srcs = [
        "tests/test_schema.rs",
    ],
    proc_macro_deps = [
        "@oak_crates_index//:async-trait",
    ],
    deps = [
        "//micro_rpc",
        "//micro_rpc_build",
        "//micro_rpc_tests/proto:test_schema_service",
        "@oak_crates_index//:maplit",
        "@oak_crates_index//:pretty_assertions",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:tokio",
    ],
)
