#
# Copyright 2025 The Project Oak 'Authors
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
load("@rules_rust//rust:defs.bzl", "rust_binary")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_binary(
    name = "oak_verity_gcp",
    srcs = ["main.rs"],
    deps = [
        "//oak_attestation_gcp",
        "//oak_attestation_types",
        "//oak_proto_rust/grpc",
        "//oak_verity/grpc:oak_verity_grpc",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:maplit",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tonic",
    ],
)

pkg_tar(
    name = "tar",
    srcs = [":oak_verity_gcp"],
    package_dir = "/usr/local/bin",
    strip_prefix = "",
)

oci_image(
    name = "image",
    base = "@distroless_cc_debian12",
    entrypoint = ["/usr/local/bin/oak_verity_gcp"],
    exposed_ports = ["8080/tcp"],
    # https://cloud.google.com/confidential-computing/confidential-space/docs/create-customize-workloads#launch_policies
    labels = {
        "tee.launch_policy.log_redirect": "always",
    },
    tars = [":tar"],
)

oci_push(
    name = "image_push",
    image = ":image",
    repository = "europe-west1-docker.pkg.dev/oak-examples-477357/c0n741n3r-1m4635/oak_verity",
)
