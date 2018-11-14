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

# TODO: Use plain cc_proto_library for the rules below.

asylo_grpc_proto_library(
    name = "deployment_service_grpc_proto",
    srcs = ["deployment_service.proto"],
)

asylo_grpc_proto_library(
    name = "execution_service_grpc_proto",
    srcs = ["execution_service.proto"],
)

asylo_grpc_proto_library(
    name = "scheduling_service_grpc_proto",
    srcs = ["scheduling_service.proto"],
)
