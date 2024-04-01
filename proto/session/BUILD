#
# Copyright 2022 The Project Oak Authors
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
load("@io_grpc_grpc_java//:java_grpc_library.bzl", "java_grpc_library")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

proto_library(
    name = "messages_proto",
    srcs = ["messages.proto"],
    deps = [
        "//proto/attestation:endorsement_proto",
        "//proto/attestation:evidence_proto",
        "//proto/crypto:crypto_proto",
    ],
)

cc_proto_library(
    name = "messages_cc_proto",
    deps = [":messages_proto"],
)

java_proto_library(
    name = "messages_java_proto",
    deps = [":messages_proto"],
)

proto_library(
    name = "service_streaming_proto",
    srcs = ["service_streaming.proto"],
    deps = [":messages_proto"],
)

proto_library(
    name = "service_unary_proto",
    srcs = ["service_unary.proto"],
    deps = [":messages_proto"],
)

cc_proto_library(
    name = "service_streaming_cc_proto",
    deps = [":service_streaming_proto"],
)

cc_grpc_library(
    name = "service_streaming_cc_grpc",
    srcs = [":service_streaming_proto"],
    grpc_only = True,
    deps = [":service_streaming_cc_proto"],
)

cc_proto_library(
    name = "service_unary_cc_proto",
    deps = [":service_unary_proto"],
)

cc_grpc_library(
    name = "service_unary_cc_grpc",
    srcs = [":service_unary_proto"],
    generate_mocks = True,
    grpc_only = True,
    deps = [":service_unary_cc_proto"],
)

java_proto_library(
    name = "service_streaming_java_proto",
    deps = [":service_streaming_proto"],
)

java_grpc_library(
    name = "service_streaming_java_grpc",
    srcs = [":service_streaming_proto"],
    deps = [":service_streaming_java_proto"],
)

java_proto_library(
    name = "service_unary_java_proto",
    deps = [":service_unary_proto"],
)

java_grpc_library(
    name = "service_unary_java_grpc",
    srcs = [":service_unary_proto"],
    deps = [":service_unary_java_proto"],
)

build_test(
    name = "build_test",
    targets = [
        ":messages_proto",
        ":service_streaming_cc_grpc",
        ":service_streaming_java_grpc",
        ":service_unary_cc_grpc",
        ":service_unary_java_grpc",
    ],
)
