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

load("@rules_proto//proto:defs.bzl", "proto_library")
load("//bazel/rust/proto:build_defs.bzl", "rust_proto_library")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

proto_library(
    name = "arbiter_proto",
    srcs = [
        "arbiter.proto",
    ],
    deps = [
        "//proto/attestation:endorsement_proto",
        "//proto/attestation:evidence_proto",
    ],
)

rust_proto_library(
    name = "arbiter_rust_proto",
    srcs = [
        ":arbiter_proto",
    ],
    extern_paths = {
        ".oak.attestation.v1": "::oak_proto_rust::oak::attestation::v1",
    },
    deps = [
        "//oak_proto_rust",
    ],
)
