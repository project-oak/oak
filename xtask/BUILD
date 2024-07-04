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
    name = "lib",
    srcs = glob(
        ["src/*.rs"],
        exclude = ["src/main.rs"],
    ),
    crate_features = ["bazel"],
    crate_name = "xtask",
    data = [
        "//oak_functions_launcher",
    ],
    proc_macro_deps = [
        "@oak_crates_index//:async-trait",
        "@oak_crates_index//:async-recursion",
        "@oak_crates_index//:strum_macros",
    ],
    rustc_env = {
        # TODO: b/351201245 - Remove when we stop using cargo to build protos.
        "WORKSPACE_ROOT": ".",
    },
    deps = [
        "@oak_crates_index//:chrono",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:clap_complete",
        "@oak_crates_index//:colored",
        "@oak_crates_index//:itertools",
        "@oak_crates_index//:nix",
        "@oak_crates_index//:once_cell",
        "@oak_crates_index//:portpicker",
        "@oak_crates_index//:regex",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:strum",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:toml",
        "@oak_crates_index//:walkdir",
    ],
)

# TODO(b/330178457) Swap ./script to use Bazel.
rust_binary(
    name = "xtask",
    srcs = ["src/main.rs"],
    deps = [
        ":lib",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:clap_complete",
        "@oak_crates_index//:colored",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:toml",
    ],
)
