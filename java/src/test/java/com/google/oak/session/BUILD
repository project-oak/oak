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

load("@rules_java//java:defs.bzl", "java_test")
load("@rules_kotlin//kotlin:jvm.bzl", "kt_jvm_library")
load("@rules_rust//rust:defs.bzl", "rust_library")
load("//bazel/jvm:defs.bzl", "oak_jvm_jni_library")

package(
    licenses = ["notice"],
)

java_test(
    name = "session_test",
    srcs = ["OakSessionTest.java"],
    test_class = "com.google.oak.session.OakSessionTest",
    deps = [
        "//java/src/main/java/com/google/oak/session:client_session",
        "//java/src/main/java/com/google/oak/session:exception",
        "//java/src/main/java/com/google/oak/session:server_session",
        "//java/src/main/java/com/google/oak/session:session_config_builder",
        "//proto/session:session_java_proto",
        "@com_google_protobuf//:protobuf_javalite",
        "@junit_junit",
    ],
)

rust_library(
    name = "attestation_publisher_test_rust",
    srcs = ["attestation_publisher_test_jni.rs"],
    deps = [
        "//java/src/main/java/com/google/oak/session/jni:oak_jni_attestation_publisher",
        "//oak_proto_rust",
        "//oak_sdk/common:oak_sdk_common",
        "//oak_session",
        "@oak_crates_index//:jni",
        "@oak_crates_index//:prost",
    ],
    alwayslink = 1,
)

oak_jvm_jni_library(
    name = "attestation_publisher_test_jni",
    linkshared = True,
    deps = [
        "attestation_publisher_test_rust",
    ],
)

kt_jvm_library(
    name = "attestation_publisher_test_lib",
    testonly = True,
    srcs = ["AttestationPublisherTest.kt"],
    deps = [
        "//java/src/main/java/com/google/oak/session:attestation_publisher",
        "//java/src/main/java/com/google/oak/session:client_session",
        "//java/src/main/java/com/google/oak/session:server_session",
        "//java/src/main/java/com/google/oak/session:session_config_builder",
        "//proto:variant_java_proto",
        "//proto/attestation:assertion_java_proto",
        "//proto/attestation:endorsement_java_proto",
        "//proto/attestation:eventlog_java_proto",
        "//proto/attestation:evidence_java_proto",
        "//proto/session:messages_java_proto",
        "//proto/session:session_java_proto",
        "@com_google_protobuf//:protobuf_java",
        "@com_google_truth_truth",
        "@junit_junit",
    ],
)

java_test(
    name = "AttestationPublisherTest",
    test_class = "com.google.oak.session.AttestationPublisherTest",
    runtime_deps = [
        ":attestation_publisher_test_jni",
        ":attestation_publisher_test_lib",
    ],
)
