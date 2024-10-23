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
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_library(
    name = "lib",
    srcs = [
        "src/app_client.rs",
        "src/demo_transport.rs",
        "src/http_service.rs",
        "src/launcher_args.rs",
        "src/lib.rs",
        "src/service.rs",
        "tests/integration_test.rs",
    ],
    crate_features = ["bazel"],
    crate_name = "oak_containers_hello_world_untrusted_app",
    proc_macro_deps = [
        "@oak_crates_index//:async-trait",
    ],
    deps = [
        "//oak_client",
        "//oak_containers/examples/hello_world/proto:hello_world_rust_proto",
        "//oak_containers/launcher:lib",
        "//oak_crypto",
        "//oak_functions_test_utils",
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:async-stream",
        "@oak_crates_index//:bytes",
        "@oak_crates_index//:futures",
        "@oak_crates_index//:http-body-util",
        "@oak_crates_index//:hyper",
        "@oak_crates_index//:hyper-util",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tonic",
        "@oak_crates_index//:which",
    ],
)

rust_binary(
    name = "oak_containers_hello_world_untrusted_app",
    srcs = ["src/main.rs"],
    crate_features = ["bazel"],
    deps = [
        ":lib",
        "//oak_client",
        "//oak_containers/launcher:lib",
        "//oak_crypto",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:log",
        "@oak_crates_index//:tokio",
    ],
)
