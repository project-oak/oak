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
load("@io_bazel_rules_go//proto:def.bzl", "go_proto_library")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

proto_library(
    name = "application_proto",
    srcs = ["application.proto"],
    deps = ["@com_google_protobuf//:wrappers_proto"],
)

cc_proto_library(
    name = "application_cc_proto",
    deps = [":application_proto"],
)

cc_grpc_library(
    name = "application_cc_grpc",
    srcs = [":application_proto"],
    grpc_only = True,
    well_known_protos = True,
    deps = [":application_cc_proto"],
)

proto_library(
    name = "grpc_encap_proto",
    srcs = ["grpc_encap.proto"],
    deps = [
        "//third_party/google/rpc:status_proto",
    ],
)

cc_proto_library(
    name = "grpc_encap_cc_proto",
    deps = [":grpc_encap_proto"],
)

proto_library(
    name = "oak_abi_proto",
    srcs = ["oak_abi.proto"],
)

cc_proto_library(
    name = "oak_abi_cc_proto",
    deps = [":oak_abi_proto"],
)

proto_library(
    name = "handle_proto",
    srcs = ["handle.proto"],
    deps = ["@com_google_protobuf//:descriptor_proto"],
)

proto_library(
    name = "label_proto",
    srcs = ["label.proto"],
    deps = [],
)

cc_proto_library(
    name = "label_cc_proto",
    deps = [":label_proto"],
)

go_proto_library(
    name = "label_go_proto",
    compilers = ["@io_bazel_rules_go//proto:go_grpc"],
    importpath = "github.com/project-oak/oak/oak/proto/label",
    proto = ":label_proto",
)

proto_library(
    name = "log_proto",
    srcs = ["log.proto"],
    deps = [],
)

cc_proto_library(
    name = "log_cc_proto",
    deps = [":log_proto"],
)

proto_library(
    name = "storage_service_proto",
    srcs = ["storage_service.proto"],
    deps = [
        ":label_proto",
    ],
)

cc_proto_library(
    name = "storage_service_cc_proto",
    deps = [":storage_service_proto"],
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

proto_library(
    name = "roughtime_service_proto",
    srcs = ["roughtime_service.proto"],
)

cc_proto_library(
    name = "roughtime_service_cc_proto",
    deps = [":roughtime_service_proto"],
)
