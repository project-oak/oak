load("@com_google_protobuf//bazel:proto_library.bzl", "proto_library")
load("//micro_rpc_build:build_defs.bzl", "rust_micro_rpc_service")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

proto_library(
    name = "proto",
    srcs = ["aead.proto"],
    deps = [
        "//proto/micro_rpc:options_proto",
        "@com_google_protobuf//:descriptor_proto",
    ],
)

rust_micro_rpc_service(
    name = "service",
    srcs = [":proto"],
)
