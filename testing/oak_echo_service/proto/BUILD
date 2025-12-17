load("@com_google_protobuf//bazel:proto_library.bzl", "proto_library")
load("//micro_rpc_build:build_defs.bzl", "rust_micro_rpc_service")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

proto_library(
    name = "proto",
    srcs = ["oak_echo.proto"],
    deps = [
        "//proto/attestation:endorsement_proto",
        "//proto/attestation:evidence_proto",
        "//proto/crypto:crypto_proto",
        "//proto/micro_rpc:options_proto",
        "@com_google_protobuf//:any_proto",
        "@com_google_protobuf//:descriptor_proto",
        "@com_google_protobuf//:duration_proto",
        "@com_google_protobuf//:empty_proto",
        "@com_google_protobuf//:timestamp_proto",
    ],
)

rust_micro_rpc_service(
    name = "service",
    srcs = [":proto"],
    extern_paths = {
        ".oak.attestation.v1": "::oak_proto_rust::oak::attestation::v1",
    },
    deps = [
        "//oak_proto_rust",
    ],
)
