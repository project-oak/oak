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

load("@rules_oci//oci:defs.bzl", "oci_image", "oci_push")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

# /bin is a symlink to usr/bin in Ubuntu 24.04; target /usr/bin so the layer does not replace the symlink.
pkg_tar(
    name = "proxy_bin_tar",
    srcs = ["//oak_proxy/server"],
    package_dir = "/usr/bin",
    target_compatible_with = ["@platforms//os:linux"],
)

pkg_tar(
    name = "proxy_config_tar",
    srcs = ["oak_proxy_server.toml"],
    mode = "0444",
    package_dir = "/etc",
    target_compatible_with = ["@platforms//os:linux"],
)

oci_image(
    name = "model_base",
    base = "@ollama_linux_amd64",
    entrypoint = [
        "/bin/server",
        "--config=/etc/oak_proxy_server.toml",
    ],
    env = {
        "OLLAMA_DEBUG": "false",
        "OLLAMA_HOST": "127.0.0.1:11434",
        # Keep model weights loaded in memory indefinitely (default is 5m).
        "OLLAMA_KEEP_ALIVE": "-1",
        "OLLAMA_MODELS": "/models",
        # Logs only server lifecycle and connection events; request payloads are never logged.
        "RUST_LOG": "info",
    },
    exposed_ports = ["8080/tcp"],
    # Omit allow_cmd_override so callers cannot bypass oak_proxy_server under this image digest.
    labels = {
        "tee.launch_policy.allow_env_override": "CONTAINER_IMAGE",
        "tee.launch_policy.log_redirect": "always",
    },
    tags = ["manual"],
    target_compatible_with = ["@platforms//os:linux"],
    tars = [
        ":proxy_bin_tar",
        ":proxy_config_tar",
    ],
)

oci_image(
    name = "image_gemma4_e2b_it_qat",
    base = ":model_base",
    tags = ["manual"],
    target_compatible_with = ["@platforms//os:linux"],
    tars = ["@ollama_gemma4_e2b_it_qat//:layers"],
)

oci_push(
    name = "push_gemma4_e2b_it_qat",
    image = ":image_gemma4_e2b_it_qat",
    remote_tags = ["latest"],
    repository = "us-east5-docker.pkg.dev/oak-examples-477357/oak-trusted-agent/model/gemma4-e2b-it-qat",
    tags = ["manual"],
    target_compatible_with = ["@platforms//os:linux"],
)
