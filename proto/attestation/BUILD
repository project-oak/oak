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

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

proto_library(
    name = "attachment_proto",
    srcs = ["attachment.proto"],
    deps = ["//proto:digest_proto"],
)

cc_proto_library(
    name = "attachment_cc_proto",
    deps = [":attachment_proto"],
)

java_proto_library(
    name = "attachment_java_proto",
    deps = [":attachment_proto"],
)

proto_library(
    name = "dice_proto",
    srcs = ["dice.proto"],
    deps = [":evidence_proto"],
)

cc_proto_library(
    name = "dice_cc_proto",
    deps = [":dice_proto"],
)

java_proto_library(
    name = "dice_java_proto",
    deps = [":dice_proto"],
)

proto_library(
    name = "endorsement_proto",
    srcs = ["endorsement.proto"],
)

cc_proto_library(
    name = "endorsement_cc_proto",
    deps = [":endorsement_proto"],
)

java_proto_library(
    name = "endorsement_java_proto",
    deps = [":endorsement_proto"],
)

proto_library(
    name = "evidence_proto",
    srcs = ["evidence.proto"],
)

cc_proto_library(
    name = "evidence_cc_proto",
    deps = [":evidence_proto"],
)

java_proto_library(
    name = "evidence_java_proto",
    deps = [":evidence_proto"],
)

proto_library(
    name = "expected_value_proto",
    srcs = ["expected_value.proto"],
    deps = [
        ":reference_value_proto",
        ":tcb_version_proto",
        "//proto:digest_proto",
    ],
)

proto_library(
    name = "reference_value_proto",
    srcs = ["reference_value.proto"],
    deps = [
        ":tcb_version_proto",
        "//proto:digest_proto",
    ],
)

cc_proto_library(
    name = "reference_value_cc_proto",
    deps = [":reference_value_proto"],
)

java_proto_library(
    name = "reference_value_java_proto",
    deps = [":reference_value_proto"],
)

proto_library(
    name = "tcb_version_proto",
    srcs = ["tcb_version.proto"],
)

cc_proto_library(
    name = "tcb_version_cc_proto",
    deps = [":tcb_version_proto"],
)

java_proto_library(
    name = "tcb_version_java_proto",
    deps = [":tcb_version_proto"],
)

proto_library(
    name = "verification_proto",
    srcs = ["verification.proto"],
    deps = [
        ":tcb_version_proto",
        "//proto:digest_proto",
    ],
)

cc_proto_library(
    name = "verification_cc_proto",
    deps = [":verification_proto"],
)

java_proto_library(
    name = "verification_java_proto",
    deps = [":verification_proto"],
)

proto_library(
    name = "eventlog_proto",
    srcs = ["eventlog.proto"],
    deps = ["@com_google_protobuf//:any_proto"],
)

cc_proto_library(
    name = "eventlog_cc_proto",
    deps = [":eventlog_proto"],
)

build_test(
    name = "build_test",
    targets = [
        ":attachment_proto",
        ":attachment_cc_proto",
        ":attachment_java_proto",
        ":dice_proto",
        ":dice_cc_proto",
        ":dice_java_proto",
        ":eventlog_proto",
        ":eventlog_cc_proto",
        ":endorsement_proto",
        ":endorsement_cc_proto",
        ":endorsement_java_proto",
        ":evidence_proto",
        ":evidence_cc_proto",
        ":evidence_java_proto",
        ":reference_value_proto",
        ":reference_value_cc_proto",
        ":reference_value_java_proto",
        ":tcb_version_proto",
        ":tcb_version_cc_proto",
        ":tcb_version_java_proto",
        ":verification_proto",
        ":verification_cc_proto",
        ":verification_java_proto",
    ],
)
