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

load("@rules_oci//oci:defs.bzl", "oci_image", "oci_load")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("@rules_rust//rust:defs.bzl", "rust_test_suite")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_test_suite(
    name = "oak_proxy_integration_test",
    srcs = ["tests/integration_test.rs"],
    data = [
        "//oak_proxy/client",
        "//oak_proxy/server",
        "//oak_proxy/testdata",
    ],
    deps = [
        "//oak_proxy/lib:oak_proxy_lib",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:log",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:toml",
    ],
)

pkg_tar(
    name = "oak_proxy_tar",
    srcs = [
        "//oak_proxy/client",
        "//oak_proxy/server",
    ],
    package_dir = "/bin",
)

filegroup(
    name = "config",
    srcs = ["proxy_client.toml"],
)

pkg_tar(
    name = "config_tar",
    srcs = [":config"],
    package_dir = "/etc",
)

oci_image(
    name = "oak_proxy_image",
    base = "@distroless_cc_debian12",
    # Docker image starts an Oak Proxy client. Corresponding server URL must be
    # specified in the CMD arguments for the ENTRYPOINT.
    entrypoint = ["/bin/client"],
    exposed_ports = ["8080/tcp"],
    labels = {
        # CMD arguments will be limited to the oak_proxy executable, specified
        # in the ENTRYPOINT.
        # See https://docs.docker.com/reference/dockerfile/#cmd
        "tee.launch_policy.allow_cmd_override": "true",
        # Logs from the open-sourced code are permitted.
        "tee.launch_policy.log_redirect": "always",
    },
    tars = [
        ":oak_proxy_tar",
        ":config_tar",
    ],
)

oci_load(
    name = "oak_proxy_load_image",
    image = ":oak_proxy_image",
    repo_tags = ["oak-proxy:latest"],
)
