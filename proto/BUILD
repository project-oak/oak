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
load("@rules_cc//cc:defs.bzl", "cc_proto_library")
load("@rules_java//java:defs.bzl", "java_proto_library")
load("@rules_proto//proto:defs.bzl", "proto_library")

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

build_test(
    name = "build_test",
    targets = [
        ":digest_proto",
        ":digest_cc_proto",
        ":digest_java_proto",
    ],
)
