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

load("@rules_rust//cargo:defs.bzl", "cargo_build_script")
load("@rules_rust//rust:defs.bzl", "rust_library")
load("//bazel:defs.bzl", "either_platform")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_library(
    name = "micro_rpc",
    srcs = glob(["src/*.rs"]),
    proc_macro_deps = [
        "@oak_crates_index//:async-trait",
        "@oak_crates_index//:prost-derive",
    ],
    target_compatible_with = either_platform([
        "//:x86_64-linux-setting",
        "//:x86_64-none-setting",
        "//:x86_64-none-no_avx-setting",
        "//:wasm32-none-setting",
    ]),
    deps = [
        ":build",
        "@oak_crates_index//:prost",
    ],
)

cargo_build_script(
    name = "build",
    srcs = [
        "build.rs",
    ],
    build_script_env = {
        "PROTOC": "$(execpath @com_google_protobuf//:protoc)",
    },
    crate_features = ["bazel"],  # See b/340185847 and fix_prost_derives function doc.
    data = [
        "//proto/micro_rpc:messages_proto",
    ],
    tools = [
        "@com_google_protobuf//:protoc",
    ],
    deps = [
        "//micro_rpc_build",
        "//oak_proto_build_utils",
    ],
)
