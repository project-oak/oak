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

load("@rules_cc//cc:defs.bzl", "cc_library")
load("@rules_android//android:rules.bzl", "android_binary", "android_library")

package(
    licenses = ["notice"],
)

cc_library(
    name = "native_client",
    srcs = ["cpp/client.cc"],
    copts = ["-std=c++11"],
    deps = [
        "//examples/hello_world/proto:hello_world_cc_grpc",
        "//oak/client:application_client",
        "//oak/client:manager_client",
        "//oak/common:utils",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/flags:flag",
        "@com_google_absl//absl/flags:parse",
        "@com_google_absl//absl/memory",
        "@com_google_asylo//asylo/util:logging",
    ],
    alwayslink = 1,
)

android_library(
    name = "client_activity",
    srcs = ["java/com/google/oak/hello_world/MainActivity.java"],
    custom_package = "com.google.oak.hello_world",
    manifest = "AndroidManifest.xml",
    resource_files = glob(["java/com/google/oak/hello_world/res/**"]),
    deps = [":native_client"],
)

android_binary(
    name = "client_app",
    custom_package = "com.google.oak.hello_world",
    manifest = "AndroidManifest.xml",
    deps = [":client_activity"],
)
