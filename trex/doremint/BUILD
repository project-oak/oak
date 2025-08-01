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
    compile_data = ["//trex/doremint/data:rekor_public_key.pem"],
    deps = [
        "//trex/endorsement",
        "//trex/sigstore",
        "//trex/sigstore_client",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:base64",
        "@oak_crates_index//:chrono",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:oci-client",
        "@oak_crates_index//:oci-spec",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde_json",
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
        "//trex/doremint/testdata:golden.json",
    ],
    env = {"CLI": "$(location :doremint)"},
)
