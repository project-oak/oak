#
# Copyright 2021 The Project Oak Authors
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
load("@com_google_protobuf//bazel:cc_proto_library.bzl", "cc_proto_library")
load("@com_google_protobuf//bazel:java_proto_library.bzl", "java_proto_library")
load("@com_google_protobuf//bazel:proto_library.bzl", "proto_library")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

proto_library(
    name = "abi_proto",
    srcs = ["abi.proto"],
    deps = ["@com_google_protobuf//:empty_proto"],
)

java_proto_library(
    name = "abi_java_proto",
    deps = [":abi_proto"],
)

proto_library(
    name = "application_config_proto",
    srcs = ["application_config.proto"],
)

cc_proto_library(
    name = "application_config_cc_proto",
    deps = [":application_config_proto"],
)

proto_library(
    name = "lookup_data_proto",
    srcs = ["lookup_data.proto"],
)

cc_proto_library(
    name = "lookup_data_cc_proto",
    deps = [":lookup_data_proto"],
)

proto_library(
    name = "testing_proto",
    srcs = ["testing.proto"],
    deps = ["//proto/micro_rpc:options_proto"],
)

build_test(
    name = "build_test",
    targets = [
        ":abi_proto",
        ":abi_java_proto",
        ":application_config_proto",
        ":application_config_cc_proto",
        ":lookup_data_proto",
        ":lookup_data_cc_proto",
        ":testing_proto",
    ],
)
