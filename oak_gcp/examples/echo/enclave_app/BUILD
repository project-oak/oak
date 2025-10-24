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

load("@rules_oci//oci:defs.bzl", "oci_image", "oci_push")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_gcp_examples_echo_enclave_app",
    srcs = [
        "src/app.rs",
        "src/app_service.rs",
        "src/gcp.rs",
        "src/lib.rs",
    ],
    proc_macro_deps = ["@oak_crates_index//:async-trait"],
    deps = [
        "//oak_attestation",
        "//oak_attestation_types",
        "//oak_crypto",
        "//oak_gcp/examples/echo/proto:echo_rust_proto",
        "//oak_proto_rust",
        "//oak_session",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:async-stream",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:reqwest",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tonic",
    ],
)

rust_binary(
    name = "bin/oak_gcp_examples_echo_enclave_app",
    srcs = ["src/main.rs"],
    deps = [
        ":oak_gcp_examples_echo_enclave_app",
        "//oak_attestation_gcp",
        "//oak_proto_rust",
        "//tr/rekor",
        "//tr/verify_endorsement",
        "//trex/sigstore_client",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:oci-client",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:tokio",
    ],
)

pkg_tar(
    name = "tar",
    srcs = [":bin/oak_gcp_examples_echo_enclave_app"],
    package_dir = "/usr/local/bin",
    strip_prefix = "/oak_gcp/examples/echo/enclave_app/bin",
)

oci_image(
    name = "image",
    base = "@distroless_cc_debian12",
    entrypoint = ["/usr/local/bin/oak_gcp_examples_echo_enclave_app"],
    exposed_ports = ["8080/tcp"],
    labels = {"tee.launch_policy.allow_env_override": "CONTAINER_IMAGE"},
    tars = [":tar"],
)

oci_push(
    name = "push",
    image = ":image",
    remote_tags = ["latest"],
    # This repository can only be used by the Oak team. You can pass the --repository flag to
    # override it:
    #
    # $ bazel run //oak_gcp/examples/echo/enclave_app:push -- --repository=${YOUR_REPO}
    #
    repository = "europe-west1-docker.pkg.dev/oak-examples-477357/c0n741n3r-1m4635/echo_enclave_app",
)

rust_binary(
    name = "deploy",
    srcs = ["src/deploy.rs"],
    data = [
        ":claims.toml",
        ":image",
        ":push",
        "//trex/doremint",
    ],
    deps = [
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:colored",
        "@oak_crates_index//:indicatif",
        "@oak_crates_index//:rpassword",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:tempfile",
    ],
)
