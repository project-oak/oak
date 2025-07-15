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

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_library(
    name = "endorsement",
    srcs = glob(["src/**/*.rs"]),
    deps = [
        "//oak_time",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:chrono",
        "@oak_crates_index//:oci-spec",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde_json",
    ],
)

rust_test(
    name = "unit_tests",
    crate = ":endorsement",
    data = [
        "//trex/endorsement/testdata:endorsement.json",
    ],
    deps = [
        "//oak_file_utils",
        "@oak_crates_index//:googletest",
        "@oak_crates_index//:prost-types",
    ],
)
