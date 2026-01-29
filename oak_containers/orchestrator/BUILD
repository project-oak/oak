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

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_containers_orchestrator",
    srcs = [
        "src/cdi.rs",
        "src/container_runtime.rs",
        "src/dice.rs",
        "src/ipc_server.rs",
        "src/key_provisioning.rs",
        "src/launcher_client.rs",
        "src/lib.rs",
        "src/logging.rs",
    ],
    # TODO: b/368030563 - Remove this feature once all client library instances use
    # the applications keys from the event log.
    crate_features = [
        "application_keys",
    ],
    deps = [
        "//oak_attestation",
        "//oak_attestation_types",
        "//oak_attestation_verification",
        "//oak_containers/agent",
        "//oak_containers/attestation:oak_containers_attestation",
        "//oak_containers/channel",
        "//oak_crypto",
        "//oak_dice",
        "//oak_proto_rust",
        "//oak_proto_rust/grpc",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:async-stream",
        "@oak_crates_index//:bytes",
        "@oak_crates_index//:ciborium",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:coset",
        "@oak_crates_index//:hpke",
        "@oak_crates_index//:log",
        "@oak_crates_index//:nix",
        "@oak_crates_index//:oci-spec",
        "@oak_crates_index//:opentelemetry-appender-tracing",
        "@oak_crates_index//:opentelemetry-otlp",
        "@oak_crates_index//:opentelemetry_sdk",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:procfs",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:rand_core",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:syslog",
        "@oak_crates_index//:tar",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tokio-util",
        "@oak_crates_index//:tonic",
        "@oak_crates_index//:tracing",
        "@oak_crates_index//:tracing-subscriber",
        "@oak_crates_index//:walkdir",
        "@oak_crates_index//:zeroize",
    ],
)

rust_library(
    name = "oak_containers_orchestrator_no_application_keys",
    srcs = [
        "src/cdi.rs",
        "src/container_runtime.rs",
        "src/dice.rs",
        "src/ipc_server.rs",
        "src/key_provisioning.rs",
        "src/launcher_client.rs",
        "src/lib.rs",
        "src/logging.rs",
    ],
    deps = [
        "//oak_attestation",
        "//oak_attestation_types",
        "//oak_attestation_verification",
        "//oak_containers/agent",
        "//oak_containers/attestation:oak_containers_attestation",
        "//oak_containers/channel",
        "//oak_crypto",
        "//oak_dice",
        "//oak_proto_rust",
        "//oak_proto_rust/grpc",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:async-stream",
        "@oak_crates_index//:bytes",
        "@oak_crates_index//:ciborium",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:coset",
        "@oak_crates_index//:hpke",
        "@oak_crates_index//:log",
        "@oak_crates_index//:nix",
        "@oak_crates_index//:oci-spec",
        "@oak_crates_index//:opentelemetry-appender-tracing",
        "@oak_crates_index//:opentelemetry-otlp",
        "@oak_crates_index//:opentelemetry_sdk",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:procfs",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:rand_core",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:syslog",
        "@oak_crates_index//:tar",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tokio-util",
        "@oak_crates_index//:tonic",
        "@oak_crates_index//:tracing",
        "@oak_crates_index//:tracing-subscriber",
        "@oak_crates_index//:walkdir",
        "@oak_crates_index//:zeroize",
    ],
)

rust_test(
    name = "oak_containers_orchestrator_test",
    compile_data = [
        "//oak_containers/orchestrator/testdata:cdi.json",
        "//oak_containers/orchestrator/testdata:oci_spec_base.json",
        "//oak_containers/orchestrator/testdata:oci_spec_target.json",
    ],
    crate = ":oak_containers_orchestrator",
    crate_features = ["application_keys"],
    data = [
        "//oak_containers/orchestrator/testdata:test_dice",
    ],
    deps = [
        "//oak_file_utils",
    ],
)

alias(
    name = "orchestrator",
    actual = ":oak_containers_orchestrator",
)
