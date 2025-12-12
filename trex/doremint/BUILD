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

load("@rules_rust//rust:defs.bzl", "rust_binary")
load("@rules_shell//shell:sh_test.bzl", "sh_test")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_binary(
    name = "doremint",
    srcs = glob(["src/**/*.rs"]),
    deps = [
        "//oak_proto_rust",
        "//oak_time",
        "//oak_time:oak_time_std",
        "//tr/digest_util",
        "//tr/intoto",
        "//trex/client",
        "//trex/cosign_util",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:base64",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:maplit",
        "@oak_crates_index//:oci-client",
        "@oak_crates_index//:oci-spec",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:toml",
    ],
)

sh_test(
    name = "cli_tests",
    srcs = ["cli_tests.sh"],
    data = [
        ":doremint",
        "//trex/doremint/testdata:claims.toml",
        "//trex/doremint/testdata:dummy_blob.txt",
        "//trex/doremint/testdata:golden.json",
    ],
    env = {
        "CLI": "$(location :doremint)",
    },
)
