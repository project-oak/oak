#
# Copyright 2025 The Project Oak Authors
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

load("@rules_oci//oci:defs.bzl", "oci_image", "oci_load", "oci_push")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_functions_mcp_lib",
    srcs = glob(["src/*.rs"]),
    proc_macro_deps = [
        "@oak_std_crates_index//:rmcp-macros",
        "@oak_std_crates_index//:async-trait",
    ],
    deps = [
        "//micro_rpc",
        "//oak_functions_service:lib_unrestricted",
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:axum",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:futures",
        "@oak_crates_index//:log",
        "@oak_crates_index//:rmcp",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tonic",
    ],
)

rust_binary(
    name = "oak_functions_mcp_server",
    srcs = ["src/main.rs"],
    deps = [
        ":oak_functions_mcp_lib",
        "//oak_functions_service:lib_unrestricted",
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:axum",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:log",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:rmcp",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:ureq",
    ],
)

filegroup(
    name = "config",
    srcs = ["proxy.toml"],
)

pkg_tar(
    name = "oak_functions_mcp_server_tar",
    srcs = [
        ":oak_functions_mcp_server",
        "//oak_proxy/server",
    ],
    package_dir = "/bin",
)

pkg_tar(
    name = "config_tar",
    srcs = [":config"],
    package_dir = "/etc",
)

oci_image(
    name = "oak_functions_mcp_server_image",
    base = "@distroless_cc_debian12",
    entrypoint = [
        "/bin/server",
        "--config=/etc/proxy.toml",
    ],
    env = {
        "RUST_LOG": "info",
    },
    exposed_ports = ["8080/tcp"],
    labels = {
        # Confidential Space launch policy that allows specific environment variables to
        # be provided at runtime:
        # - `CONTAINER_IMAGE`: self-reference for the TEE workload which it can use to fetch endorsements.
        # - `WASM_URL`, `LOOKUP_DATA_URL`, `TOOL_CONFIG_URL` for configuring the Wasm module,
        #   lookup data, and tool config at deployment time.
        #
        # https://cloud.google.com/confidential-computing/confidential-space/docs/create-customize-workloads#launch_policies
        "tee.launch_policy.allow_env_override": "WASM_URL,LOOKUP_DATA_URL,TOOL_CONFIG_URL",
        # Logs from the open-sourced code are permitted.
        "tee.launch_policy.log_redirect": "always",
    },
    tars = [
        ":oak_functions_mcp_server_tar",
        ":config_tar",
    ],
)

oci_load(
    name = "oak_functions_mcp_server_load_image",
    image = ":oak_functions_mcp_server_image",
    repo_tags = ["oak-functions-mcp:latest"],
)

oci_push(
    name = "oak_functions_mcp_server_push",
    image = ":oak_functions_mcp_server_image",
    repository = "europe-west1-docker.pkg.dev/oak-functions-standalone/oak-functions-mcp-containers/oak-functions-mcp",
)
