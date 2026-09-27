#
# Copyright 2026 The Project Oak Authors
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
    name = "trusted_agent_proto",
    srcs = ["trusted_agent.proto"],
)

cc_proto_library(
    name = "trusted_agent_cc_proto",
    target_compatible_with = ["@platforms//os:linux"],
    deps = [":trusted_agent_proto"],
)

build_test(
    name = "build_test",
    targets = [
        ":trusted_agent_proto",
        ":trusted_agent_cc_proto",
    ],
)
