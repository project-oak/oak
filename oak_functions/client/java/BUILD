#
# Copyright 2021 The Project Oak Authors
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
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

java_library(
    name = "client",
    srcs = [
        "src/com/google/oak/functions/client/AttestationClient.java",
    ],
    deps = [
        "//grpc_attestation/proto:server_java_grpc",
        "//grpc_attestation/proto:server_java_proto",
        "//oak_functions/proto:abi_java_proto",
        "//remote_attestation/java:remote_attestation",
        "@com_google_protobuf//:protobuf_javalite",
        "@io_grpc_grpc_java//api",
        "@io_grpc_grpc_java//netty",
        "@io_grpc_grpc_java//stub",
    ],
)

# Dedicated Android target is necessary for using Tink internally.
android_library(
    name = "client_android",
    srcs = [
        "src/com/google/oak/functions/client/AttestationClient.java",
    ],
    # Exclude Android specific targets because they will not run in the main Docker Image.
    tags = ["manual"],
    deps = [
        "//grpc_attestation/proto:server_java_grpc_lite",
        "//grpc_attestation/proto:server_java_proto_lite",
        "//oak_functions/proto:abi_java_proto_lite",
        "//remote_attestation/java:remote_attestation_android",
        "@com_google_protobuf//:protobuf_javalite",
        "@io_grpc_grpc_java//api",
        "@io_grpc_grpc_java//okhttp",
        "@io_grpc_grpc_java//stub",
    ],
)
