#
# Copyright 2018 The Project Oak Authors
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

load("@com_github_grpc_grpc//bazel:cc_grpc_library.bzl", "cc_grpc_library")
load("@rules_cc//cc:defs.bzl", "cc_proto_library")
load("@rules_proto//proto:defs.bzl", "proto_library")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

proto_library(
    name = "enclave_proto",
    srcs = ["enclave.proto"],
    deps = [
        ":manager_proto",
        "@com_google_asylo//asylo:enclave_proto",
    ],
)

cc_proto_library(
    name = "enclave_cc_proto",
    deps = [":enclave_proto"],
)

proto_library(
    name = "manager_proto",
    srcs = ["manager.proto"],
)

cc_proto_library(
    name = "manager_cc_proto",
    deps = [":manager_proto"],
)

cc_grpc_library(
    name = "manager_cc_grpc",
    srcs = [":manager_proto"],
    grpc_only = True,
    well_known_protos = True,
    deps = [":manager_cc_proto"],
)

proto_library(
    name = "grpc_encap_proto",
    srcs = ["grpc_encap.proto"],
    deps = [
        "//third_party/google/rpc:status_proto",
        "@com_google_protobuf//:any_proto",
    ],
)

cc_proto_library(
    name = "grpc_encap_cc_proto",
    deps = [":grpc_encap_proto"],
)

proto_library(
    name = "oak_api_proto",
    srcs = ["oak_api.proto"],
)

cc_proto_library(
    name = "oak_api_cc_proto",
    deps = [":oak_api_proto"],
)

proto_library(
    name = "policy_proto",
    srcs = ["policy.proto"],
    deps = [],
)

cc_proto_library(
    name = "policy_cc_proto",
    deps = [":policy_proto"],
)

proto_library(
    name = "storage_channel_proto",
    srcs = ["storage_channel.proto"],
    deps = [
        ":policy_proto",
        "//third_party/google/rpc:status_proto",
    ],
)

cc_proto_library(
    name = "storage_channel_cc_proto",
    deps = [":storage_channel_proto"],
)

proto_library(
    name = "storage_proto",
    srcs = ["storage.proto"],
)

cc_proto_library(
    name = "storage_cc_proto",
    deps = [":storage_proto"],
)

cc_grpc_library(
    name = "storage_cc_grpc",
    srcs = [":storage_proto"],
    grpc_only = True,
    deps = [
        ":storage_cc_proto",
        "//third_party/google/rpc:status_cc_proto",
    ],
)
