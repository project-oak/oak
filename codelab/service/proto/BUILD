load("@com_google_protobuf//bazel:proto_library.bzl", "proto_library")
load("@oak//micro_rpc_build:build_defs.bzl", "rust_micro_rpc_service")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

proto_library(
    name = "service_proto",
    srcs = ["service.proto"],
    deps = [
        "@oak//proto/attestation:evidence_proto",
    ],
)

rust_micro_rpc_service(
    name = "echo_service",
    srcs = [":service_proto"],
    extern_paths = {
        ".oak.attestation.v1": "::oak_proto_rust::oak::attestation::v1",
    },
    deps = [
        "@oak//oak_proto_rust",
    ],
)
