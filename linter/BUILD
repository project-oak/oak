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

rust_binary(
    name = "linter",
    srcs = ["main.rs"],
    deps = [
        ":lib",
        ":tools",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:colored",
        "@oak_crates_index//:ignore",
    ],
)

rust_library(
    name = "lib",
    srcs = [
        "lib.rs",
    ],
    crate_name = "linter",
    deps = [
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:ignore",
    ],
)

rust_library(
    name = "tools",
    srcs = [
        "tools/bad_todos.rs",
        "tools/build_license.rs",
        "tools/buildifier.rs",
        "tools/clang_format.rs",
        "tools/hadolint.rs",
        "tools/lib.rs",
        "tools/markdownlint.rs",
        "tools/prettier.rs",
        "tools/rustfmt.rs",
        "tools/shell_check.rs",
        "tools/source_license.rs",
    ],
    deps = [
        ":lib",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:lazy_static",
        "@oak_crates_index//:regex",
    ],
)
