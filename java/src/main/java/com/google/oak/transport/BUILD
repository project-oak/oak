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

load("@rules_android//android:rules.bzl", "android_library")
load("@rules_java//java:defs.bzl", "java_library")

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

android_library(
    name = "transport_android",
    srcs = [
        "EvidenceProvider.java",
        "QueueingStreamObserver.java",
        "Transport.java",
    ],
    deps = [
        "//java/src/main/java/com/google/oak/util:util_android",
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

android_library(
    name = "grpc_streaming_transport_android",
    srcs = [
        "GrpcStreamingTransport.java",
    ],
    deps = [
        ":transport_android",
        "//java/src/main/java/com/google/oak/util:util_android",
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

android_library(
    name = "api_key_interceptor_android",
    srcs = ["ApiKeyInterceptor.java"],
    deps = [
        "@io_grpc_grpc_java//api",
    ],
)
