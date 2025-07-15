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

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_time",
    srcs = glob(["src/**/*.rs"]),
    crate_features = [
        "prost",
    ],
    deps = [
        "@oak_crates_index//:chrono",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:time",
    ],
)

rust_test(
    name = "oak_time_test",
    crate = ":oak_time",
    crate_features = [
        "prost",
    ],
    deps = [
        "@oak_crates_index//:googletest",
    ],
)

rust_library(
    name = "oak_time_std",
    srcs = glob(["std/**/*.rs"]),
    deps = [
        ":oak_time",
    ],
)

rust_test(
    name = "oak_time_std_test",
    crate = ":oak_time_std",
    deps = [
        "@oak_crates_index//:googletest",
    ],
)
