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

load("@rules_android//android:rules.bzl", "android_library")
load("@rules_java//java:defs.bzl", "java_library")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

java_library(
    name = "exception",
    srcs = [
        "OakSessionException.java",
    ],
)

android_library(
    name = "exception_android",
    srcs = [
        "OakSessionException.java",
    ],
)

java_library(
    name = "client_session",
    srcs = [
        "OakClientSession.java",
    ],
    deps = [
        ":exception",
        ":session_config_builder",
        "//java/src/main/java/com/google/oak/session/jni/jvm:oak_client_session_jni",
        "//proto/session:session_java_proto",
        "@com_google_protobuf//:protobuf_java",
    ],
)

java_library(
    name = "client_session_no_jni",
    srcs = [
        "OakClientSession.java",
    ],
    deps = [
        ":exception",
        ":session_config_builder_no_jni",
        "//proto/session:session_java_proto",
        "@com_google_protobuf//:protobuf_java",
    ],
)

android_library(
    name = "client_session_android",
    srcs = [
        "OakClientSession.java",
    ],
    deps = [
        ":exception_android",
        ":session_config_builder_android",
        "//java/src/main/java/com/google/oak/session/jni:oak_client_session_jni",
        "//proto/session:session_java_proto_lite",
        "@com_google_protobuf//:protobuf_javalite",
    ],
)

android_library(
    name = "client_session_no_jni_android",
    srcs = [
        "OakClientSession.java",
    ],
    deps = [
        ":exception_android",
        ":session_config_builder_no_jni_android",
        "//proto/session:session_java_proto_lite",
        "@com_google_protobuf//:protobuf_javalite",
    ],
)

java_library(
    name = "server_session",
    srcs = [
        "OakServerSession.java",
    ],
    deps = [
        ":exception",
        ":session_config_builder",
        "//java/src/main/java/com/google/oak/session/jni/jvm:oak_server_session_jni",
        "//proto/session:session_java_proto",
        "@com_google_protobuf//:protobuf_java",
    ],
)

java_library(
    name = "server_session_no_jni",
    srcs = [
        "OakServerSession.java",
    ],
    deps = [
        ":exception",
        ":session_config_builder_no_jni",
        "//proto/session:session_java_proto",
        "@com_google_protobuf//:protobuf_java",
    ],
)

android_library(
    name = "server_session_android",
    srcs = [
        "OakServerSession.java",
    ],
    deps = [
        ":exception_android",
        ":session_config_builder_android",
        "//java/src/main/java/com/google/oak/session/jni:oak_server_session_jni",
        "//proto/session:session_java_proto_lite",
        "@com_google_protobuf//:protobuf_javalite",
    ],
)

android_library(
    name = "server_session_no_jni_android",
    srcs = [
        "OakServerSession.java",
    ],
    deps = [
        ":exception_android",
        ":session_config_builder_no_jni_android",
        "//proto/session:session_java_proto_lite",
        "@com_google_protobuf//:protobuf_javalite",
    ],
)

java_library(
    name = "session_config_builder",
    srcs = ["OakSessionConfigBuilder.java"],
    deps = [
        "//java/src/main/java/com/google/oak/session/jni:oak_session_config_builder_jni",
    ],
)

java_library(
    name = "session_config_builder_no_jni",
    srcs = ["OakSessionConfigBuilder.java"],
    deps = [],
)

android_library(
    name = "session_config_builder_android",
    srcs = ["OakSessionConfigBuilder.java"],
    deps = [
        "//java/src/main/java/com/google/oak/session/jni:oak_session_config_builder_jni",
    ],
)

android_library(
    name = "session_config_builder_no_jni_android",
    srcs = ["OakSessionConfigBuilder.java"],
    deps = [],
)

java_library(
    name = "attestation_publisher",
    srcs = ["AttestationPublisher.java"],
)

android_library(
    name = "attestation_publisher_android",
    srcs = ["AttestationPublisher.java"],
)
