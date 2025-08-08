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

load("@rules_oci//oci:defs.bzl", "oci_image")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("@rules_rust//rust:defs.bzl", "rust_binary")
load("@rules_shell//shell:sh_binary.bzl", "sh_binary")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_binary(
    name = "ctf_sha2",
    srcs = ["src/main.rs"],
    deps = [
        "//oak_attestation_gcp",
        "@oak_crates_index//:rand",
        "@oak_crates_index//:sha2",
    ],
)

pkg_tar(
    name = "tar",
    srcs = [":ctf_sha2"],
    package_dir = "/usr/local/bin",
    strip_prefix = "",
)

oci_image(
    name = "image",
    base = "@distroless_cc_debian12",
    entrypoint = ["/usr/local/bin/ctf_sha2"],
    exposed_ports = [],
    # https://cloud.google.com/confidential-computing/confidential-space/docs/create-customize-workloads#launch_policies
    labels = {
        "tee.launch_policy.allow_env_override": "CONTAINER_IMAGE",
        "tee.launch_policy.log_redirect": "always",
    },
    tars = [":tar"],
)

# The following rules are used to deploy the container image to GCE.
# See ctf_sha2/README.md for more details.

IMAGE_URL = "europe-west1-docker.pkg.dev/oak-examples-477357/c0n741n3r-1m4635/ctf_sha2"

INSTANCE_NAME = "ctf-sha2-test"

ZONE = "us-west1-b"

sh_binary(
    name = "image_push",
    srcs = ["image_push.sh"],
    args = ["$(location :image)"],
    data = [":image"],
    env = {
        "IMAGE_URL": IMAGE_URL,
    },
    tags = ["manual"],
)

sh_binary(
    name = "instance_create",
    srcs = ["instance_create.sh"],
    args = ["$(location :image.json.sha256)"],
    data = [":image.json.sha256"],
    env = {
        "IMAGE_URL": IMAGE_URL,
        "INSTANCE_NAME": INSTANCE_NAME,
        "ZONE": ZONE,
    },
    tags = ["manual"],
)

sh_binary(
    name = "instance_update",
    srcs = ["instance_update.sh"],
    args = ["$(location :image.json.sha256)"],
    data = [":image.json.sha256"],
    env = {
        "IMAGE_URL": IMAGE_URL,
        "INSTANCE_NAME": INSTANCE_NAME,
        "ZONE": ZONE,
    },
    tags = ["manual"],
)

sh_binary(
    name = "instance_reset",
    srcs = ["instance_reset.sh"],
    env = {
        "INSTANCE_NAME": INSTANCE_NAME,
        "ZONE": ZONE,
    },
    tags = ["manual"],
)

sh_binary(
    name = "instance_start",
    srcs = ["instance_start.sh"],
    env = {
        "INSTANCE_NAME": INSTANCE_NAME,
        "ZONE": ZONE,
    },
    tags = ["manual"],
)
