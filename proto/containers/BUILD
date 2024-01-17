#
# Copyright 2023 The Project Oak Authors
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

load("@bazel_skylib//rules:build_test.bzl", "build_test")
load("@com_github_grpc_grpc//bazel:cc_grpc_library.bzl", "cc_grpc_library")
load("@com_github_grpc_grpc//bazel:python_rules.bzl", "py_grpc_library", "py_proto_library")
load("@rules_cc//cc:defs.bzl", "cc_proto_library")
load("@rules_proto//proto:defs.bzl", "proto_library")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

proto_library(
    name = "common_proto",
    srcs = ["common.proto"],
)

proto_library(
    name = "application_interfaces_proto",
    srcs = ["application_interfaces.proto"],
    deps = [
        ":common_proto",
        "//oak_crypto/proto/v1:crypto_proto",
        "//oak_remote_attestation/proto/v1:messages_proto",
        "@com_google_protobuf//:empty_proto",
    ],
)

cc_proto_library(
    name = "application_interfaces_cc_proto",
    deps = [":application_interfaces_proto"],
)

cc_grpc_library(
    name = "application_interfaces_cc_grpc",
    srcs = [":application_interfaces_proto"],
    grpc_only = True,
    deps = [":application_interfaces_proto"],
)

py_proto_library(
    name = "application_interfaces_py_proto",
    deps = [":application_interfaces_proto"],
)

py_grpc_library(
    name = "application_interfaces_py_grpc",
    srcs = [":application_interfaces_proto"],
    deps = [":application_interfaces_py_proto"],
)

proto_library(
    name = "launcher_proto",
    srcs = ["launcher.proto"],
    deps = [
        ":common_proto",
    ],
)

proto_library(
    name = "hostlib_key_provisioning_proto",
    srcs = ["hostlib_key_provisioning.proto"],
    deps = [
        "//proto/key_provisioning:key_provisioning_proto",
    ],
)

# TODO(#4392): Remove once the migration is complete.
proto_library(
    name = "orchestrator_crypto_proto",
    srcs = ["orchestrator_crypto.proto"],
    deps = [
        "//oak_crypto/proto/v1:crypto_proto",
    ],
)

build_test(
    name = "build_test",
    targets = [
        ":hostlib_key_provisioning_proto",
        ":application_interfaces_proto",
        ":launcher_proto",
    ],
)
