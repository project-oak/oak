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
load("//bazel:defs.bzl", "oci_runtime_bundle")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_binary(
    name = "enclave_app",
    srcs = ["enclave_app.rs"],
    deps = [
        "//ctf_sha2/containers/proto:tonic_service",
        "//oak_proto_rust",
        "//oak_proto_rust/grpc",
        "//oak_sdk/containers:oak_sdk_containers",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:rand",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tonic",
    ],
)

pkg_tar(
    name = "tar",
    srcs = [":enclave_app"],
    package_dir = "/usr/local/bin",
    strip_prefix = "/ctf_sha2/containers",
)

oci_image(
    name = "image",
    base = "@distroless_cc_debian12",
    entrypoint = ["/usr/local/bin/enclave_app"],
    tars = [":tar"],
)

oci_runtime_bundle(
    name = "bundle",
    image = ":image",
)

rust_binary(
    name = "host_app",
    srcs = ["host_app.rs"],
    data = [
        ":bundle",
        "//oak_containers/kernel:bzImage",
        "//oak_containers/stage1_bin:stage1_cpio",
        "//oak_containers/system_image:oak_containers_system_image",
        "//stage0_bin",
    ],
    deps = [
        "//ctf_sha2/containers/proto:tonic_service",
        "//oak_containers/launcher:lib",
        "//oak_file_utils",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:log",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tonic",
        "@oak_crates_index//:which",
    ],
)

rust_binary(
    name = "arbiter",
    srcs = ["arbiter.rs"],
    deps = [
        "//ctf_sha2/containers/proto:tonic_service",
        "//falsify",
        "//oak_attestation_verification",
        "//oak_proto_rust",
        "//tr/key_util",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:log",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:x509-cert",
    ],
)
