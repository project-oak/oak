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

package(
    default_visibility = ["//visibility:public"],
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
        "//oak_crypto/proto/v1:crypto_java_proto_lite",
        "//oak_remote_attestation/proto/v1:messages_java_proto_lite",
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
        "//oak_crypto/proto/v1:crypto_java_proto_lite",
        "//oak_remote_attestation/proto/v1:messages_java_proto_lite",
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
        "//oak_crypto/proto/v1:crypto_java_proto",
        "//oak_remote_attestation/proto/v1:messages_java_proto",
        "//oak_remote_attestation/proto/v1:service_streaming_java_proto",
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
        "//oak_crypto/proto/v1:crypto_java_proto",
        "//oak_remote_attestation/proto/v1:messages_java_proto",
        "//oak_remote_attestation/proto/v1:service_streaming_java_proto",
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
