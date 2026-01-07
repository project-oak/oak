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
load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library", "rust_test")

package(
    licenses = ["notice"],
)

rust_binary(
    name = "linter",
    srcs = ["main.rs"],
    deps = [
        ":lib",
        ":tools",
        "@crates//:clap",
        "@crates//:colored",
        "@crates//:ignore",
    ],
)

rust_library(
    name = "lib",
    srcs = [
        "lib.rs",
    ],
    crate_name = "linter",
    deps = [
        "@crates//:anyhow",
        "@crates//:ignore",
    ],
)

rust_library(
    name = "tools",
    srcs = glob(["tools/*.rs"]),
    deps = [
        ":lib",
        "@crates//:anyhow",
        "@crates//:lazy_static",
        "@crates//:regex",
    ],
)

rust_test(
    name = "tools_test",
    crate = ":tools",
)
