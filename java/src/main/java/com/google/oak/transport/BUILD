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

load("@rules_java//java:defs.bzl", "java_library")
load("@rules_kotlin//kotlin:jvm.bzl", "kt_jvm_library")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

java_library(
    name = "transport",
    srcs = [
        "EvidenceProvider.java",
        "QueueingStreamObserver.java",
        "Transport.java",
    ],
    deps = [
        "//java/src/main/java/com/google/oak/util",
        "//proto/crypto:crypto_java_proto",
        "//proto/session:messages_java_proto",
        "@io_grpc_grpc_java//api",
        "@io_grpc_grpc_java//stub",
    ],
)

java_library(
    name = "transport_android",
    srcs = [
        "EvidenceProvider.java",
        "QueueingStreamObserver.java",
        "Transport.java",
    ],
    deps = [
        "//java/src/main/java/com/google/oak/util",
        "//proto/crypto:crypto_java_proto",
        "//proto/session:messages_java_proto",
        "@io_grpc_grpc_java//api",
        "@io_grpc_grpc_java//stub",
    ],
)

java_library(
    name = "grpc_streaming_transport",
    srcs = [
        "GrpcStreamingTransport.java",
    ],
    deps = [
        ":transport",
        "//java/src/main/java/com/google/oak/util",
        "//proto/crypto:crypto_java_proto",
        "//proto/session:messages_java_proto",
        "//proto/session:service_streaming_java_proto",
        "@io_grpc_grpc_java//stub",
    ],
)

java_library(
    name = "grpc_streaming_transport_android",
    srcs = [
        "GrpcStreamingTransport.java",
    ],
    deps = [
        ":transport_android",
        "//java/src/main/java/com/google/oak/util",
        "//proto/crypto:crypto_java_proto",
        "//proto/session:messages_java_proto",
        "//proto/session:service_streaming_java_proto",
        "@io_grpc_grpc_java//stub",
    ],
)

java_library(
    name = "api_key_interceptor",
    srcs = ["ApiKeyInterceptor.java"],
    deps = [
        "@io_grpc_grpc_java//api",
    ],
)

java_library(
    name = "api_key_interceptor_android",
    srcs = ["ApiKeyInterceptor.java"],
    deps = [
        "@io_grpc_grpc_java//api",
    ],
)

kt_jvm_library(
    name = "session_transport",
    srcs = [
        "SessionTransport.kt",
    ],
    deps = [
    ],
)

kt_jvm_library(
    name = "grpc_session_v1_client_transport",
    srcs = [
        "GrpcSessionV1ClientTransport.kt",
    ],
    runtime_deps = [
        "@maven//:com_google_flogger_flogger_system_backend",
    ],
    deps = [
        ":session_transport",
        "//proto/services:session_v1_service_kt_grpc",
        "//proto/session:session_java_proto",
        "@io_grpc_grpc_java//api",
        "@maven//:com_google_flogger_google_extensions",
        "@maven//:org_jetbrains_kotlinx_kotlinx_coroutines_core",
    ],
)
