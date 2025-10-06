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

load("@aspect_bazel_lib//lib:write_source_files.bzl", "write_source_files")
load("@rules_rust//cargo:defs.bzl", "cargo_build_script")
load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_test(
    name = "oak_proto_serialization_test",
    srcs = ["test/serde_test.rs"],
    deps = [
        ":oak_proto_rust",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:serde_json",
    ],
)

rust_library(
    name = "oak_proto_rust",
    srcs = glob(["src/**"]),
    proc_macro_deps = [
        "@oak_crates_index//:prost-derive",
    ],
    deps = [
        ":build",
        "@oak_crates_index//:base64",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:serde",
    ],
)

cargo_build_script(
    name = "build",
    srcs = [
        "build.rs",
    ],
    build_script_env = {
        "PROTOC": "$(execpath @com_google_protobuf//:protoc)",
        "DESCRIPTOR_PROTO_PATH": "$(location @com_google_protobuf//:descriptor_proto_srcs)",
    },
    data = [
        "//proto:digest.proto",
        "//proto:validity.proto",
        "//proto:variant.proto",
        "//proto/attestation:assertion.proto",
        "//proto/attestation:attachment.proto",
        "//proto/attestation:dice.proto",
        "//proto/attestation:endorsement.proto",
        "//proto/attestation:eventlog.proto",
        "//proto/attestation:evidence.proto",
        "//proto/attestation:expected_value.proto",
        "//proto/attestation:reference_value.proto",
        "//proto/attestation:tcb_version.proto",
        "//proto/attestation:verification.proto",
        "//proto/containers:hostlib_key_provisioning.proto",
        "//proto/containers:interfaces.proto",
        "//proto/containers:orchestrator_crypto.proto",
        "//proto/crypto:certificate.proto",
        "//proto/crypto:crypto.proto",
        "//proto/ctf_sha2:falsify.proto",
        "//proto/key_provisioning:key_provisioning.proto",
        "//proto/micro_rpc:options.proto",
        "//proto/oak_debug/service:oak_debug.proto",
        "//proto/oak_functions:abi.proto",
        "//proto/oak_functions:application_config.proto",
        "//proto/oak_functions:lookup_data.proto",
        "//proto/oak_functions:testing.proto",
        "//proto/oak_functions/sdk:oak_functions_wasm.proto",
        "//proto/oak_functions/service:oak_functions.proto",
        "//proto/oak_functions/standalone:oak_functions_session.proto",
        "//proto/oak_verity:oak_verity.proto",
        "//proto/packages:packages.proto",
        "//proto/restricted_kernel:initial_data.proto",
        "//proto/session:messages.proto",
        "//proto/session:service_streaming.proto",
        "//proto/session:session.proto",
        "//third_party/google:profile.proto",
        "@com_google_protobuf//:descriptor_proto_srcs",
        "@com_google_protobuf//:well_known_type_protos",
    ],
    tools = [
        "@com_google_protobuf//:protoc",
    ],
    deps = [
        ":annotation",
        "//oak_proto_build_utils",
        "@oak_crates_index//:prost-build",
        "@oak_crates_index//:serde",
    ],
)

rust_library(
    name = "annotation",
    srcs = ["annotation.rs"],
    deps = [
        "//oak_proto_build_utils",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-build",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:serde",
    ],
)

# Prost build tools aren't available internally, so we copy the generated files
# into the source tree for easy import. See README.md for more details.
write_source_files(
    name = "copy_generated_files",
    files = {
        "generated": "//oak_proto_rust:build",
    },
)
