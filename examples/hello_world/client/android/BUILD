#
# Copyright 2019 The Project Oak Authors
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

load("@rules_android//android:rules.bzl", "android_binary", "android_library")
load("@rules_java//java:defs.bzl", "java_lite_proto_library")

package(
    licenses = ["notice"],
)

java_lite_proto_library(
    name = "label_java_proto_lite",
    deps = ["//oak_abi/proto:label_proto"],
)

android_library(
    name = "client_activity",
    srcs = ["java/com/google/oak/hello_world/MainActivity.java"],
    custom_package = "com.google.oak.hello_world",
    manifest = "AndroidManifest.xml",
    resource_files = glob(["java/com/google/oak/hello_world/res/**"]),
    deps = [
        ":label_java_proto_lite",
        "//examples/hello_world/proto:hello_world_java_grpc",
        "//examples/hello_world/proto:hello_world_java_proto_lite",
        "@io_grpc_grpc_java//api",
        "@io_grpc_grpc_java//core",
        "@io_grpc_grpc_java//okhttp",
        "@io_grpc_grpc_java//protobuf",
        "@io_grpc_grpc_java//stub",
    ],
)

android_binary(
    name = "client_app",
    custom_package = "com.google.oak.hello_world",
    manifest = "AndroidManifest.xml",
    deps = [
        ":client_activity",
        "//examples/certs:local_certs",
    ],
)
