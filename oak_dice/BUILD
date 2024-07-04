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

rust_library(
    name = "oak_dice",
    srcs = glob(["src/**"]),
    crate_features = [
        "no_std",
    ],
    target_compatible_with = [
        "//:x86_64-none-setting",
    ],
    deps = [
        "@oak_crates_index//:static_assertions",
        "@oak_crates_index//:strum",
        "@oak_crates_index//:zerocopy",
    ] + select({
        # TODO: b/347706173 - Try to reduce / remove items in this select by moving all to no_std.
        "@platforms//os:none": [
            "@oak_no_std_crates_index//:bitflags",
            "@oak_no_std_crates_index//:ciborium",
            "@oak_no_std_crates_index//:coset",
            "@oak_no_std_crates_index//:hex",
            "@oak_no_std_crates_index//:hkdf",
            "@oak_no_std_crates_index//:p256",
            "@oak_no_std_crates_index//:rand_core",
            "@oak_no_std_crates_index//:sha2",
            "@oak_no_std_crates_index//:zeroize",
        ],
        "//conditions:default": [
            "@oak_crates_index//:bitflags",
            "@oak_crates_index//:ciborium",
            "@oak_crates_index//:coset",
            "@oak_crates_index//:hex",
            "@oak_crates_index//:hkdf",
            "@oak_crates_index//:p256",
            "@oak_crates_index//:rand_core",
            "@oak_crates_index//:sha2",
            "@oak_crates_index//:zeroize",
        ],
    }),
)
