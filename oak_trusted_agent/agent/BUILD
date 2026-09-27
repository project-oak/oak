#
# Copyright 2026 The Project Oak Authors
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
load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library", "rust_test")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_trusted_agent_lib",
    srcs = ["src/lib.rs"],
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        "@oak_crates_index//:log",
        "@oak_crates_index//:thiserror",
        "@oak_crates_index//:url",
    ],
)

rust_binary(
    name = "oak_trusted_agent",
    srcs = ["src/main.rs"],
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        ":oak_trusted_agent_lib",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:log",
        "@oak_crates_index//:tokio",
    ],
)

rust_test(
    name = "oak_trusted_agent_tests",
    size = "small",
    crate = ":oak_trusted_agent_lib",
    data = glob(["config/*.toml"]),
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        "//oak_file_utils",
        "//oak_proxy/lib:oak_proxy_lib",
        "@oak_crates_index//:googletest",
    ],
)

filegroup(
    name = "config",
    srcs = glob(["config/*.toml"]),
)

pkg_tar(
    name = "agent_bin_tar",
    srcs = [
        ":oak_trusted_agent",
        "//oak_proxy/client",
        "//oak_proxy/server",
    ],
    package_dir = "/bin",
    target_compatible_with = ["@platforms//os:linux"],
)

pkg_tar(
    name = "agent_config_tar",
    srcs = [
        ":config",
        "//oak_attestation_gcp:data/confidential_space_root.pem",
    ],
    mode = "0444",
    package_dir = "/etc",
    target_compatible_with = ["@platforms//os:linux"],
)

oci_image(
    name = "image",
    base = "@distroless_cc_debian13_linux_amd64",
    entrypoint = ["/bin/oak_trusted_agent"],
    env = {
        "RUST_LOG": "info",
    },
    exposed_ports = ["8080/tcp"],
    # Confidential Space launch policy allowing operator-configured runtime
    # endpoints:
    # - `CONTAINER_IMAGE`: self-reference used by the TEE workload to fetch
    #   endorsements.
    # - `MODEL_PROXY_URL`, `MCP_PROXY_URLS`, `SYSTEM_PROMPT_URL`: dynamically
    #   assigned service endpoints and system prompt configuration.
    #
    # https://cloud.google.com/confidential-computing/confidential-space/docs/create-customize-workloads#launch_policies
    labels = {
        "tee.launch_policy.allow_env_override": "CONTAINER_IMAGE,MODEL_PROXY_URL,MCP_PROXY_URLS,SYSTEM_PROMPT_URL",
        "tee.launch_policy.log_redirect": "always",
    },
    target_compatible_with = ["@platforms//os:linux"],
    tars = [
        ":agent_bin_tar",
        ":agent_config_tar",
    ],
)

oci_load(
    name = "load_image",
    image = ":image",
    repo_tags = ["oak-trusted-agent:latest"],
    target_compatible_with = ["@platforms//os:linux"],
)

oci_push(
    name = "push",
    image = ":image",
    remote_tags = ["latest"],
    repository = "us-east5-docker.pkg.dev/oak-examples-477357/oak-trusted-agent/agent",
    target_compatible_with = ["@platforms//os:linux"],
)
