load("@rules_proto//proto:defs.bzl", "proto_library")

package(
    default_visibility = ["//micro_rpc_tests:__subpackages__"],
    licenses = ["notice"],
)

proto_library(
    name = "test_schema_proto",
    srcs = ["test_schema.proto"],
    deps = [
        "//proto/micro_rpc:options_proto",
        "@com_google_protobuf//:any_proto",
        "@com_google_protobuf//:duration_proto",
        "@com_google_protobuf//:empty_proto",
        "@com_google_protobuf//:timestamp_proto",
    ],
)
