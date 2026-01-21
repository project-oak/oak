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
load("@rules_shell//shell:sh_test.bzl", "sh_test")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_library(
    name = "lib",
    srcs = glob(
        ["src/**"],
        exclude = ["src/main.rs"],
    ),
    crate_name = "oak_functions_containers_launcher",
    proc_macro_deps = [
        "@oak_crates_index//:async-trait",
    ],
    deps = [
        "//oak_containers/launcher:lib",
        "//oak_crypto",
        "//oak_functions_launcher:lib",
        "//oak_proto_rust",
        "//oak_proto_rust/grpc",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:async-stream",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:futures",
        "@oak_crates_index//:hyper-util",
        "@oak_crates_index//:log",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-vsock",
        "@oak_crates_index//:tonic",
        "@oak_crates_index//:tower",
        "@oak_crates_index//:ubyte",
    ],
)

rust_test(
    name = "unit_tests",
    crate = ":lib",
)

rust_binary(
    name = "oak_functions_containers_launcher",
    srcs = ["src/main.rs"],
    deps = [
        ":lib",
        "//oak_containers/launcher:lib",
        "//oak_functions_launcher:lib",
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:log",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:ubyte",
    ],
)

rust_test(
    name = "oak_functions_containers_launcher_test_bin",
    srcs = ["tests/integration_test.rs"],
    data = [
        ":oak_functions_containers_launcher",
        "//cc/client:cli",
        "//java/src/main/java/com/google/oak/client/oak_functions_client",
        "//oak_containers/kernel",
        "//oak_functions/examples/echo",
        "//oak_functions/examples/key_value_lookup",
        "//oak_functions_containers_app:bundle",
        "//oak_functions_launcher:mock_lookup_data",
    ],
    # Don't run this test directly, as it requires nswrap to work.
    tags = ["manual"],
    deps = [
        "//oak_client",
        "//oak_file_utils",
        "//oak_functions_client:lib",
        "//oak_functions_test_utils",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:log",
        "@oak_crates_index//:tokio",
    ],
)

sh_test(
    name = "oak_functions_containers_launcher_test",
    srcs = ["tests/run_integration_test.sh"],
    args = ["$(location :oak_functions_containers_launcher_test_bin)"],
    data = [
        ":oak_functions_containers_launcher_test_bin",
        "//oak_containers/launcher:nswrap",
    ],
)
