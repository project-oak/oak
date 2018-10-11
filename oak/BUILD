licenses(["notice"])  # Apache v2.0

package(
    default_visibility = ["//visibility:public"],
)

load(
    "@com_google_asylo//asylo/bazel:asylo.bzl",
    "enclave_loader",
    "sim_enclave",
)
load(
    "@com_google_asylo//asylo/bazel:proto.bzl",
    "asylo_proto_library",
    "asylo_grpc_proto_library",
)

asylo_proto_library(
    name = "oak_proto",
    srcs = ["oak.proto"],
    deps = ["@com_google_asylo//asylo:enclave_proto"],
)

asylo_grpc_proto_library(
    name = "oak_server_grpc_proto",
    srcs = ["oak_server.proto"],
)

cc_library(
    name = "oak_server",
    srcs = ["oak_server.cc"],
    hdrs =  ["oak_server.h"],
    deps = [
        ":oak_server_grpc_proto",
        "@com_github_grpc_grpc//:grpc++",
    ],
)

sim_enclave(
    name = "oak_enclave.so",
    srcs = [
        "oak_enclave.cc",
    ],
    deps = [
        ":oak_proto_cc",
        ":oak_server",
        "@com_google_absl//absl/memory",
        "@com_google_absl//absl/strings",
        "@com_google_asylo//asylo/grpc/auth:grpc++_security_enclave",
        "@com_google_asylo//asylo/grpc/auth:null_credentials_options",
        "@com_google_asylo//asylo:enclave_runtime",
        "@com_google_asylo//asylo/grpc/util:enclave_server",
        "@com_google_asylo//asylo/util:status",
        "//wac:wa",
    ],
)

enclave_loader(
    name = "oak",
    srcs = ["oak_driver.cc"],
    enclaves = {"enclave": ":oak_enclave.so"},
    loader_args = ["--enclave_path='{enclave}'"],
    deps = [
        ":oak_proto_cc",
        "@com_github_gflags_gflags//:gflags_nothreads",
        "@com_google_absl//absl/strings",
        "@com_google_absl//absl/synchronization",
        "@com_google_absl//absl/time",
        "@com_google_asylo//asylo:enclave_client",
        "@com_google_asylo//asylo/util:logging",
        "@com_google_asylo//asylo/grpc/util:enclave_server_proto_cc",
    ],
)
