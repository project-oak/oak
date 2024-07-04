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

load("@rules_rust//rust:defs.bzl", "rust_library")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

DEPS = [
    "//micro_rpc",
    "//oak_functions_abi",
    "//oak_proto_rust",
    "@oak_crates_index//:spinning_top",
    "@oak_no_std_crates_index//:anyhow",
    "@oak_no_std_crates_index//:log",
    "@oak_no_std_crates_index//:prost",
    "@oak_no_std_crates_index//:rand_core",
    "@oak_no_std_crates_index//:wasmi",
]

rust_library(
    name = "oak_functions_service",
    srcs = glob(["src/**"]),
    # The features are inverted on purpose; this means the "default" package will not have sensitive logging enabled.
    crate_features = ["deny_sensitive_logging"],
    target_compatible_with = [
        "@platforms//os:none",
    ],
    deps = DEPS,
)

rust_library(
    name = "oak_functions_service_allow_sensitive_logging",
    srcs = glob(["src/**"]),
    target_compatible_with = [
        "@platforms//os:none",
    ],
    deps = DEPS,
)
