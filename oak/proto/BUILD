#
# Copyright 2018 Project Oak authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

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
    name = "scheduling_service_grpc_proto",
    srcs = ["scheduling_service.proto"],
)

asylo_grpc_proto_library(
    name = "execution_service_grpc_proto",
    srcs = ["execution_service.proto"],
)
