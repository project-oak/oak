#
# Copyright 2020 The Project Oak Authors
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

load("@io_bazel_rules_rust//rust:rust.bzl", "rust_binary")

package(
    licenses = ["notice"],
)

rust_binary(
    name = "oak_loader",
    srcs = glob(["src/**/*.rs"]),
    crate_features = [
        "oak_debug",
    ],
    edition = "2018",
    deps = [
        "//cargo:anyhow",
        "//cargo:log",
        "//cargo:prost",
        "//cargo:signal_hook",
        "//cargo:simple_logger",
        "//cargo:structopt",
        "//oak/server/rust/oak_runtime",
    ],
)
