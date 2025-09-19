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

load("@rules_rust//rust:defs.bzl", "rust_binary")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_binary(
    name = "rekor_cli",
    srcs = glob(["**/*.rs"]),
    # TODO: b/445140472 - Clean up access to Rekor public key in entire repo.
    compile_data = ["//oak_attestation_verification/testdata:endorsement"],
    deps = [
        "//tr/key_util",
        "//tr/rekor",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
    ],
)
