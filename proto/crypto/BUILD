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
load("@com_google_protobuf//bazel:java_lite_proto_library.bzl", "java_lite_proto_library")
load("@com_google_protobuf//bazel:java_proto_library.bzl", "java_proto_library")
load("@com_google_protobuf//bazel:proto_library.bzl", "proto_library")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

proto_library(
    name = "certificate_proto",
    srcs = ["certificate.proto"],
    deps = [
        "//proto:validity_proto",
        "@com_google_protobuf//:timestamp_proto",
    ],
)

cc_proto_library(
    name = "certificate_cc_proto",
    deps = [":certificate_proto"],
)

java_proto_library(
    name = "certificate_java_proto",
    deps = [":certificate_proto"],
)

java_lite_proto_library(
    name = "certificate_java_proto_lite",
    deps = [":certificate_proto"],
)

proto_library(
    name = "crypto_proto",
    srcs = ["crypto.proto"],
)

cc_proto_library(
    name = "crypto_cc_proto",
    deps = [":crypto_proto"],
)

java_proto_library(
    name = "crypto_java_proto",
    deps = [":crypto_proto"],
)

java_lite_proto_library(
    name = "crypto_java_proto_lite",
    deps = [":crypto_proto"],
)

build_test(
    name = "build_test",
    targets = [
        ":certificate_proto",
        ":certificate_cc_proto",
        ":certificate_java_proto",
        ":certificate_java_proto_lite",
        ":crypto_proto",
        ":crypto_cc_proto",
        ":crypto_java_proto",
        ":crypto_java_proto_lite",
    ],
)
