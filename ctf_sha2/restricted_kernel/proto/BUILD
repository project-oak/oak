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

load("//micro_rpc_build:build_defs.bzl", "extern", "micro_rpc_service")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

micro_rpc_service(
    name = "service",
    srcs = [":service.proto"],
    externs = [
        extern(".oak.attestation.v1", "oak_proto_rust::oak::attestation::v1", "//oak_proto_rust"),
    ],
    proto_package_name = "oak.ctf_sha2.enclave",
    deps = [
        "//proto:digest.proto",
        "//proto/attestation:eventlog.proto",
        "//proto/attestation:evidence.proto",
        "@com_google_protobuf//:well_known_type_protos",
    ],
)
