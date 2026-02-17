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

# Ideally, the target name should be just `digest`, and `crate_name`
# should be `oak_digest`, but `crate_name` is not supported internally.
rust_library(
    name = "oak_digest",
    srcs = [
        "lib.rs",
    ],
    deps = [
        "//oak_proto_rust",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:thiserror",
    ],
)

rust_test(
    name = "digest_test",
    crate = ":oak_digest",
)
