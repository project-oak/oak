#
# Copyright 2024 The Project Oak Authors
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
load("@com_google_protobuf//bazel:java_proto_library.bzl", "java_proto_library")
load("@com_google_protobuf//bazel:proto_library.bzl", "proto_library")
load("@io_grpc_grpc_java//:java_grpc_library.bzl", "java_grpc_library")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

proto_library(
    name = "session_v1_service_proto",
    srcs = ["session_v1_service.proto"],
    deps = ["//proto/session:session_proto"],
)

cc_proto_library(
    name = "session_v1_service_cc_proto",
    deps = [":session_v1_service_proto"],
)

cc_grpc_library(
    name = "session_v1_service_cc_grpc",
    srcs = [":session_v1_service_proto"],
    grpc_only = True,
    deps = [":session_v1_service_cc_proto"],
)

java_proto_library(
    name = "session_v1_service_java_proto",
    deps = [":session_v1_service_proto"],
)

java_grpc_library(
    name = "session_v1_service_java_grpc",
    srcs = [":session_v1_service_proto"],
    deps = [":session_v1_service_java_proto"],
)

build_test(
    name = "build_test",
    targets = [
        ":session_v1_service_proto",
        ":session_v1_service_cc_proto",
        ":session_v1_service_cc_grpc",
        ":session_v1_service_java_proto",
        ":session_v1_service_java_grpc",
    ],
)
