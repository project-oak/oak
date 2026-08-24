#
# Copyright 2026 The Project Oak Authors
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

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_test")
load("//oak_containers/app_base:defs.bzl", "app_bundle")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_test(
    name = "key_handling_test",
    size = "medium",
    srcs = [
        "key_handling_test.rs",
    ],
    args = ["--test-threads=1"],
    data = [
        "//oak_containers/kernel",
        "//oak_containers/stage1_bin:insecure_stage1_cpio",
        "//stage0_bin",
    ],
    target_compatible_with = [
        "@platforms//cpu:x86_64",
        "@platforms//os:linux",
    ],
    deps = [
        "//oak_file_utils",
        "//oak_test_utils",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:googletest",
    ],
)
