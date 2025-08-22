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

load("@rules_oci//oci:defs.bzl", "oci_image", "oci_load")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library", "rust_test")
load("//bazel:defs.bzl", "oci_runtime_bundle")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

exports_files(["README.md"])

rust_library(
    name = "lib",
    srcs = [
        "src/lib.rs",
        "tests/integration_test.rs",
    ],
    compile_data = [":README.md"],
    crate_features = [
        "deny_sensitive_logging",
    ],
    crate_name = "oak_functions_standalone",
    deps = [
        "//micro_rpc",
        "//oak_attestation",
        "//oak_attestation_types",
        "//oak_debug_service",
        "//oak_functions_service:lib_unrestricted",
        "//oak_proto_rust",
        "//oak_proto_rust/grpc",
        "//oak_session",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:async-stream",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tonic",
        "@oak_crates_index//:tower",
    ],
)

rust_binary(
    name = "oak_functions_standalone",
    srcs = ["src/main.rs"],
    crate_features = [
        "deny_sensitive_logging",
    ],
    deps = [
        ":lib",
        "//oak_attestation_gcp",
        "//oak_crypto",
        "//oak_functions_service:lib_unrestricted",
        "//oak_proto_rust",
        "//oak_session",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:log",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:tikv-jemallocator",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:ureq",
    ],
)

rust_test(
    name = "lib_test",
    crate = ":lib",
)

rust_test(
    name = "oak_functions_standalone_integration_test",
    size = "large",
    srcs = ["tests/integration_test.rs"],
    data = [
        "//oak_functions/examples/echo",
        "//oak_functions/examples/key_value_lookup",
    ],
    deps = [
        ":lib",
        "//micro_rpc",
        "//oak_client",
        "//oak_functions_client:lib",
        "//oak_functions_service:lib_unrestricted",
        "//oak_functions_test_utils",
        "//oak_launcher_utils",
        "//oak_proto_rust",
        "//oak_proto_rust/grpc",
        "//oak_session",
        "@oak_crates_index//:futures",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tonic",
    ],
)

pkg_tar(
    name = "oak_functions_standalone_tar",
    srcs = [
        ":oak_functions_standalone",
        "//oak_functions/examples/echo",
        "//oak_functions/examples/key_value_lookup",
        "//oak_functions_standalone/testdata:fake_weather_data.binarypb",
    ],
    package_dir = "/usr/local/bin",
)

oci_image(
    name = "oak_functions_standalone_image",
    base = "@distroless_cc_debian12",
    entrypoint = ["/usr/local/bin/oak_functions_standalone"],
    exposed_ports = ["8080/tcp"],
    # https://cloud.google.com/confidential-computing/confidential-space/docs/create-customize-workloads#launch_policies
    labels = {
        # CMD arguments will be limited to the oak_functions_standalone
        # executable, specified in the ENTRYPOINT.
        # See https://docs.docker.com/reference/dockerfile/#cmd
        "tee.launch_policy.allow_cmd_override": "true",
        # Logs from the open-sourced code are permitted.
        "tee.launch_policy.log_redirect": "always",
    },
    tars = [":oak_functions_standalone_tar"],
)

oci_load(
    name = "oak_functions_standalone_load_image",
    image = ":oak_functions_standalone_image",
    repo_tags = ["oak_functions_standalone:latest"],
)

oci_runtime_bundle(
    name = "bundle",
    image = ":oak_functions_standalone_image",
)
