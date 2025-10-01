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

# TODO: b/427550226 - Make this work on Mac OS.
rust_binary(
    name = "endorscope_cli",
    srcs = glob(["*.rs"]),
    deps = [
        "//oak_file_utils",
        "//oak_proto_rust",
        "//tr/endorscope",
        "//tr/intoto",
        "//tr/rekor",
        "//tr/verify_endorsement",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:url",
    ],
)
