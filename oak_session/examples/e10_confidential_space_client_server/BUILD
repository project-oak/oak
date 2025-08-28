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
load("@rules_rust//rust:defs.bzl", "rust_binary")
load("@rules_shell//shell:sh_test.bzl", "sh_test")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_binary(
    name = "main",
    srcs = ["main.rs"],
    compile_data = [
        "//oak_session/examples/e10_confidential_space_client_server/data:binding_key.pem",
        "//oak_session/examples/e10_confidential_space_client_server/data:root_ca_cert.pem",
        "//oak_session/examples/e10_confidential_space_client_server/data:token.jwt",
    ],
    deps = [
        "//oak_attestation",
        "//oak_attestation_gcp",
        "//oak_attestation_verification",
        "//oak_attestation_verification_types",
        "//oak_proto_rust",
        "//oak_session",
        "//oak_time",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:x509-cert",
    ],
)

sh_test(
    name = "main_test",
    srcs = ["main_test.sh"],
    data = [":main"],
    env = {"PROGRAM": "$(location :main)"},
)
