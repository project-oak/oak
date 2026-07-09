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

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_lint_runner_lib",
    srcs = [
        "src/config.rs",
        "src/identify.rs",
        "src/lib.rs",
        "src/run.rs",
        "src/ui.rs",
    ],
    crate_name = "oak_lint_runner",
    crate_root = "src/lib.rs",
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:colored",
        "@oak_crates_index//:content_inspector",
        "@oak_crates_index//:futures",
        "@oak_crates_index//:ignore",
        "@oak_crates_index//:indicatif",
        "@oak_crates_index//:num_cpus",
        "@oak_crates_index//:regex",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:shlex",
        "@oak_crates_index//:tokei",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:toml",
    ],
)

rust_binary(
    name = "oak_lint_runner",
    srcs = ["src/main.rs"],
    crate_root = "src/main.rs",
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        ":oak_lint_runner_lib",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:colored",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:toml",
    ],
)
