package(
    default_visibility = ["//visibility:public"],
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
