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
load("@com_google_protobuf//bazel:cc_proto_library.bzl", "cc_proto_library")
load("@com_google_protobuf//bazel:proto_library.bzl", "proto_library")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

proto_library(
    name = "oak_debug_proto",
    srcs = ["oak_debug.proto"],
    deps = [
        "//third_party/google:profile_proto",
        "@com_google_protobuf//:duration_proto",
    ],
)

cc_proto_library(
    name = "oak_debug_cc_proto",
    deps = [":oak_debug_proto"],
)

build_test(
    name = "build_test",
    targets = [
        ":oak_debug_proto",
        ":oak_debug_cc_proto",
    ],
)
