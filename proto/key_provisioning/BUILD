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
load("@rules_proto//proto:defs.bzl", "proto_library")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

proto_library(
    name = "key_provisioning_proto",
    srcs = ["key_provisioning.proto"],
)

build_test(
    name = "build_test",
    targets = [
        ":dice_proto",
        ":dice_cc_proto",
        ":dice_java_proto",
        ":endorsement_proto",
        ":endorsement_cc_proto",
        ":endorsement_java_proto",
        ":evidence_proto",
        ":evidence_cc_proto",
        ":evidence_java_proto",
        ":reference_value_proto",
        ":reference_value_cc_proto",
        ":reference_value_java_proto",
        ":verification_proto",
        ":verification_cc_proto",
        ":verification_java_proto",
    ],
)
