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
load("@rules_rust//rust:defs.bzl", "rust_library")
load("//bazel:defs.bzl", "either_platform")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_proto_rust",
    srcs = glob(["src/**"]),
    proc_macro_deps = [
        "@oak_crates_index//:prost-derive",
    ],
    target_compatible_with = either_platform([
        "@platforms//os:linux",
        "@platforms//os:none",
    ]),
    deps = [
        ":build",
        "//micro_rpc",
    ] + select({
        "@platforms//os:none": [
            "//third_party/prost-types",
            "@oak_no_std_crates_index//:prost",
        ],
        "//conditions:default": [
            # See comment on micro_rpc/BUILD.
            "@oak_crates_index//:prost",
            "@oak_crates_index//:prost-types",
        ],
    }),
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
    crate_features = ["bazel"],  # See b/340185847 and fix_prost_derives function doc.
    data = [
        "//proto:digest_proto",
        "//proto/attestation:attachment_proto",
        "//proto/attestation:dice_proto",
        "//proto/attestation:endorsement_proto",
        "//proto/attestation:eventlog_proto",
        "//proto/attestation:evidence_proto",
        "//proto/attestation:expected_value_proto",
        "//proto/attestation:reference_value_proto",
        "//proto/attestation:tcb_version_proto",
        "//proto/attestation:verification_proto",
        "//proto/containers:hello_world_proto",
        "//proto/containers:interfaces_proto",
        "//proto/crypto:crypto_proto",
        "//proto/oak_functions:abi_proto",
        "//proto/oak_functions:application_config_proto",
        "//proto/oak_functions:lookup_data_proto",
        "//proto/oak_functions:testing_proto",
        "//proto/oak_functions/sdk:oak_functions_wasm_proto",
        "//proto/oak_functions/service:oak_functions_proto",
        "//proto/session:session_proto",
        "@com_google_protobuf//:descriptor_proto_srcs",
        "@com_google_protobuf//:well_known_type_protos",
    ],
    tools = [
        "@com_google_protobuf//:protoc",
    ],
    deps = [
        "//micro_rpc_build",
        "//oak_proto_build_utils",
        "@oak_crates_index//:prost-build",
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
