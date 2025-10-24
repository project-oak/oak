#
# Copyright 2023 The Project Oak Authors
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
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

micro_rpc_service(
    name = "micro_rpc_noise_rust_proto",
    srcs = [":micro_rpc_noise.proto"],
    externs = [
        extern(".oak", "oak_proto_rust::oak", "//oak_proto_rust"),
    ],
    proto_package_name = "oak.containers.example",
    deps = [
        "//proto:digest.proto",
        "//proto:validity.proto",
        "//proto:variant.proto",
        "//proto/attestation:assertion.proto",
        "//proto/attestation:endorsement.proto",
        "//proto/attestation:eventlog.proto",
        "//proto/attestation:evidence.proto",
        "//proto/crypto:certificate.proto",
        "//proto/crypto:crypto.proto",
        "//proto/micro_rpc:options.proto",
        "//proto/session:messages.proto",
        "//proto/session:session.proto",
        "@com_google_protobuf//:well_known_type_protos",
    ],
)
