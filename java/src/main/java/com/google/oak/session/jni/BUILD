#
# Copyright 2024 The Project Oak Authors
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

load("@rules_rust//rust:defs.bzl", "rust_library")
load("//bazel/android:defs.bzl", "oak_android_jni_library")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_client_session_rust",
    srcs = ["oak_client_session_jni.rs"],
    deps = [
        "//oak_proto_rust",
        "//oak_session",
        "@oak_crates_index//:jni",
        "@oak_crates_index//:prost",
    ],
    alwayslink = 1,
)

oak_android_jni_library(
    name = "oak_client_session_jni",
    linkshared = True,
    deps = [
        ":oak_client_session_rust",
        ":oak_session_config_builder_rust",
    ],
)

rust_library(
    name = "oak_server_session_rust",
    srcs = ["oak_server_session_jni.rs"],
    deps = [
        "//oak_proto_rust",
        "//oak_session",
        "@oak_crates_index//:jni",
        "@oak_crates_index//:prost",
    ],
    alwayslink = 1,
)

oak_android_jni_library(
    name = "oak_server_session_jni",
    linkshared = True,
    deps = [
        ":oak_server_session_rust",
        ":oak_session_config_builder_rust",
    ],
)

rust_library(
    name = "oak_session_config_builder_rust",
    srcs = ["oak_session_config_builder_jni.rs"],
    deps = [
        "//oak_proto_rust",
        "//oak_session",
        "@oak_crates_index//:jni",
        "@oak_crates_index//:prost",
    ],
    alwayslink = 1,
)

oak_android_jni_library(
    name = "oak_session_config_builder_jni",
    linkshared = True,
    deps = [
        ":oak_session_config_builder_rust",
    ],
)
