load("@aspect_bazel_lib//lib:write_source_files.bzl", "write_source_files")
load("@rules_rust//cargo:defs.bzl", "cargo_build_script")
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
        ":build",
        "//micro_rpc",
        "//micro_rpc_build",
        "@oak_crates_index//:maplit",
        "@oak_crates_index//:pretty_assertions",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:tokio",
    ],
)

cargo_build_script(
    name = "build",
    srcs = [
        "build.rs",
    ],
    build_script_env = {
        "PROTOC": "$(execpath @com_google_protobuf//:protoc)",
        "DESCRIPTOR_PROTO_PATH": "$(location @com_google_protobuf//:descriptor_proto_srcs)",
    },
    crate_features = ["bazel"],  # See b/340185847 and fix_prost_derives function doc.
    data = [
        "//micro_rpc_tests/proto:test_schema.proto",
        "//proto/micro_rpc:options.proto",
        "@com_google_protobuf//:descriptor_proto_srcs",
        "@com_google_protobuf//:well_known_type_protos",
    ],
    tools = [
        "@com_google_protobuf//:protoc",
    ],
    deps = [
        "//micro_rpc_build",
        "//oak_proto_build_utils",
    ],
)

# Whenever you change the test schema, run:
# bazel run micro_rpc_tests:copy_generated_to_out
# To update the reference file.
write_source_files(
    name = "write_test_schema",
    files = {
        "generated": "//micro_rpc_tests:build",
    },
)
