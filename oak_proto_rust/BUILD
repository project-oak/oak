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

load("@rules_rust//cargo:defs.bzl", "cargo_build_script")
load("@rules_rust//rust:defs.bzl", "rust_library")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_proto_rust",
    srcs = glob(["src/**"]),
    deps = [
        ":build",
        "//micro_rpc",
        "@oak_crates_index//:prost",
    ],
)

cargo_build_script(
    name = "build",
    srcs = [
        "build.rs",
    ],
    build_script_env = {
        "PROTOC": "$(execpath @com_google_protobuf//:protoc)",
    },
    data = [
        "//oak_containers/proto:interfaces_proto",
        "//proto:digest_proto",
        "//proto/attestation:attachment_proto",
        "//proto/attestation:dice_proto",
        "//proto/attestation:endorsement_proto",
        "//proto/attestation:evidence_proto",
        "//proto/attestation:expected_value_proto",
        "//proto/attestation:reference_value_proto",
        "//proto/attestation:tcb_version_proto",
        "//proto/attestation:verification_proto",
        "//proto/crypto:crypto_proto",
        "//proto/crypto:crypto_rust_prost",
        "//proto/oak_functions:abi_proto",
        "//proto/oak_functions:lookup_data_proto",
        "//proto/oak_functions:testing_proto",
        "@com_google_protobuf//:protoc",
    ],
    deps = [
        "//micro_rpc_build",
        "@oak_crates_index//:prost-build",
    ],
)
