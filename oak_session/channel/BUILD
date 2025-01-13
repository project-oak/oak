#
# Copyright 2025 The Project Oak Authors
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

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_session_channel",
    srcs = ["channel.rs"],
    proc_macro_deps = [
        "@oak_crates_index//:async-trait",
    ],
    deps = [
        "//oak_proto_rust",
        "//oak_session",
        "@oak_crates_index//:anyhow",
    ],
)

rust_library(
    name = "oak_session_channel_testing",
    srcs = ["testing.rs"],
    proc_macro_deps = [
        "@oak_crates_index//:async-trait",
    ],
    deps = [
        ":oak_session_channel",
        "//oak_proto_rust",
        "//oak_session",
        "@oak_crates_index//:anyhow",
    ],
)

rust_test(
    name = "oak_session_channel_test",
    srcs = ["tests.rs"],
    proc_macro_deps = [
        "@oak_crates_index//:async-trait",
    ],
    deps = [
        ":oak_session_channel",
        ":oak_session_channel_testing",
        "//oak_session",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:tokio",
    ],
)
