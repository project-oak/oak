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
load("@com_google_protobuf//bazel:cc_proto_library.bzl", "cc_proto_library")
load("@com_google_protobuf//bazel:proto_library.bzl", "proto_library")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

proto_library(
    name = "hostlib_key_provisioning_proto",
    srcs = ["hostlib_key_provisioning.proto"],
    deps = [
        "//proto/key_provisioning:key_provisioning_proto",
        "@com_google_protobuf//:empty_proto",
    ],
)

proto_library(
    name = "interfaces_proto",
    srcs = ["interfaces.proto"],
    deps = [
        "//proto/attestation:endorsement_proto",
        "//proto/attestation:evidence_proto",
        "//proto/session:messages_proto",
        "@com_google_protobuf//:empty_proto",
    ],
)

cc_proto_library(
    name = "interfaces_cc_proto",
    deps = [":interfaces_proto"],
)

cc_grpc_library(
    name = "interfaces_cc_grpc",
    srcs = [":interfaces_proto"],
    generate_mocks = True,
    grpc_only = True,
    deps = [":interfaces_cc_proto"],
)

proto_library(
    name = "orchestrator_crypto_proto",
    srcs = ["orchestrator_crypto.proto"],
    deps = [
        "//proto/crypto:crypto_proto",
        "//proto/session:messages_proto",
        "@com_google_protobuf//:empty_proto",
    ],
)

cc_proto_library(
    name = "orchestrator_crypto_cc_proto",
    deps = [":orchestrator_crypto_proto"],
)

cc_grpc_library(
    name = "orchestrator_crypto_cc_grpc",
    srcs = [":orchestrator_crypto_proto"],
    generate_mocks = True,
    grpc_only = True,
    deps = [":orchestrator_crypto_cc_proto"],
)

build_test(
    name = "build_test",
    targets = [
        ":hostlib_key_provisioning_proto",
        ":interfaces_proto",
        ":interfaces_cc_proto",
        ":interfaces_cc_grpc",
        ":orchestrator_crypto_proto",
        ":orchestrator_crypto_cc_proto",
        ":orchestrator_crypto_cc_grpc",
    ],
)
