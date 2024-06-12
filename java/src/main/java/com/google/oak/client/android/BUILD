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

load("@build_bazel_rules_android//android:rules.bzl", "android_binary", "android_library")

package(
    licenses = ["notice"],
)

android_library(
    name = "client_activity",
    srcs = ["MainActivity.java"],
    custom_package = "com.google.oak.client.android",
    manifest = "AndroidManifest.xml",
    resource_files = glob(["res/**"]),
    deps = [
        "//java/src/main/java/com/google/oak/client",
        "//java/src/main/java/com/google/oak/remote_attestation:insecure_attestation_verifier",
        "//java/src/main/java/com/google/oak/transport:api_key_interceptor",
        "//java/src/main/java/com/google/oak/transport:grpc_streaming_transport",
        "//java/src/main/java/com/google/oak/util",
        "//proto/session:service_streaming_java_grpc",
        "@com_google_guava_guava",
        "@com_google_protobuf//:protobuf_javalite",
        "@io_grpc_grpc_java//api",
        "@io_grpc_grpc_java//netty",
    ],
)

android_binary(
    name = "client_app",
    custom_package = "com.google.oak.client.android",
    manifest = "AndroidManifest.xml",
    multidex = "native",
    deps = [
        ":client_activity",
    ],
)
