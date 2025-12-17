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
load("@com_google_protobuf//bazel:cc_proto_library.bzl", "cc_proto_library")
load("@com_google_protobuf//bazel:java_proto_library.bzl", "java_proto_library")
load("@com_google_protobuf//bazel:proto_library.bzl", "proto_library")
load("@com_google_protobuf//bazel:py_proto_library.bzl", "py_proto_library")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

proto_library(
    name = "digest_proto",
    srcs = ["digest.proto"],
)

cc_proto_library(
    name = "digest_cc_proto",
    deps = [":digest_proto"],
)

java_proto_library(
    name = "digest_java_proto",
    deps = [":digest_proto"],
)

py_proto_library(
    name = "digest_py_pb2",
    deps = [":digest_proto"],
)

proto_library(
    name = "validity_proto",
    srcs = ["validity.proto"],
    deps = [
        "@com_google_protobuf//:duration_proto",
        "@com_google_protobuf//:timestamp_proto",
    ],
)

cc_proto_library(
    name = "validity_cc_proto",
    deps = [":validity_proto"],
)

java_proto_library(
    name = "validity_java_proto",
    deps = [":validity_proto"],
)

py_proto_library(
    name = "validity_py_pb2",
    deps = [":validity_proto"],
)

proto_library(
    name = "variant_proto",
    srcs = ["variant.proto"],
)

cc_proto_library(
    name = "variant_cc_proto",
    deps = [":variant_proto"],
)

java_proto_library(
    name = "variant_java_proto",
    deps = [":variant_proto"],
)

py_proto_library(
    name = "variant_py_pb2",
    deps = [":variant_proto"],
)

build_test(
    name = "build_test",
    targets = [
        ":digest_proto",
        ":digest_cc_proto",
        ":digest_java_proto",
        ":digest_py_pb2",
        ":validity_proto",
        ":validity_cc_proto",
        ":validity_java_proto",
        ":validity_py_pb2",
        ":variant_proto",
        ":variant_cc_proto",
        ":variant_java_proto",
        ":variant_py_pb2",
    ],
)
