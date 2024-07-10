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
load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library", "rust_test")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_library(
    name = "lib",
    srcs = glob(
        ["src/**"],
        exclude = ["src/main.rs"],
    ),
    crate_name = "oak_functions_launcher",
    proc_macro_deps = [
        "@oak_crates_index//:async-trait",
    ],
    deps = [
        ":build",
        "//micro_rpc",
        "//oak_client",
        "//oak_launcher_utils",
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:async-stream",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:futures",
        "@oak_crates_index//:hashbrown",
        "@oak_crates_index//:log",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tonic",
        "@oak_crates_index//:ubyte",
    ],
)

rust_test(
    name = "oak_functions_launcher_test",
    size = "small",
    crate = ":lib",
)

rust_binary(
    name = "oak_functions_launcher",
    srcs = ["src/main.rs"],
    deps = [
        ":lib",
        "//oak_client",
        "//oak_functions_abi",
        "//oak_launcher_utils",
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:log",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:regex",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:ubyte",
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
    crate_features = ["bazel"],
    data = [
        "//proto/session:messages_proto",
        "//proto/session:service_streaming_proto",
    ],
    tools = [
        "@com_google_protobuf//:protoc",
    ],
    deps = [
        "//oak_grpc_utils",
        "@oak_crates_index//:prost-build",
    ],
)
