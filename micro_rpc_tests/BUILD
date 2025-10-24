load("@aspect_bazel_lib//lib:write_source_files.bzl", "write_source_files")
load("@rules_rust//rust:defs.bzl", "rust_test")
load("//micro_rpc_build:build_defs.bzl", "micro_rpc_service")

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
        ":service_build",
        "//micro_rpc",
        "//micro_rpc_build",
        "@oak_crates_index//:maplit",
        "@oak_crates_index//:pretty_assertions",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:tokio",
    ],
)

micro_rpc_service(
    name = "service",
    srcs = ["//micro_rpc_tests:proto/test_schema.proto"],
    proto_package_name = "micro_rpc.tests",
    deps = [
        "//proto/micro_rpc:options.proto",
        "@com_google_protobuf//:well_known_type_protos",
    ],
)

# Whenever you change the test schema, run:
# bazel run micro_rpc_tests:copy_generated_to_out
# To update the reference file.
write_source_files(
    name = "write_test_schema",
    files = {
        "generated": ":service_build",
    },
)
