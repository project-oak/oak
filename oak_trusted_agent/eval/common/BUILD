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

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_visibility = ["//oak_trusted_agent:__subpackages__"],
    licenses = ["notice"],
)

# Statement construction, signing and decoding, shared by both binaries.
rust_library(
    name = "oak_trusted_agent_eval_common",
    srcs = [
        "envelope.rs",
        "flags.rs",
        "lib.rs",
        "statement.rs",
        "tests.rs",
    ],
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        "//oak_attestation_types",
        "//oak_proto_rust",
        "//tr/intoto",
        "//util/digest:oak_digest",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:base64",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde_json",
    ],
)

alias(
    name = "common",
    actual = ":oak_trusted_agent_eval_common",
)

rust_test(
    name = "oak_trusted_agent_eval_common_test",
    crate = ":oak_trusted_agent_eval_common",
    target_compatible_with = ["@platforms//os:linux"],
    deps = ["@oak_crates_index//:tempfile"],
)
