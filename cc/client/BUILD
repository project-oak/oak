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

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

# Libraries

cc_library(
    name = "client",
    srcs = ["client.cc"],
    hdrs = ["client.h"],
    deps = [
        "//cc/attestation/verification:attestation_verifier",
        "//cc/crypto:client_encryptor",
        "//cc/crypto:common",
        "//cc/transport",
        "//proto/attestation:endorsement_cc_proto",
        "//proto/attestation:evidence_cc_proto",
        "//proto/attestation:verification_cc_proto",
        "//proto/crypto:crypto_cc_proto",
        "//proto/session:messages_cc_proto",
        "@com_google_absl//absl/memory",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
    ],
)

# Tests

cc_test(
    name = "client_test",
    size = "small",
    srcs = ["client_test.cc"],
    deps = [
        ":client",
        "//cc/attestation/verification:attestation_verifier",
        "//cc/crypto:encryption_key",
        "//cc/crypto:server_encryptor",
        "//cc/crypto/hpke:recipient_context",
        "//cc/transport",
        "//proto/attestation:evidence_cc_proto",
        "//proto/session:messages_cc_proto",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
        "@com_google_googletest//:gtest_main",
    ],
)

# Binaries

cc_binary(
    name = "cli",
    srcs = ["grpc_client_cli.cc"],
    deps = [
        ":client",
        "//cc/attestation/verification:insecure_attestation_verifier",
        "//cc/transport:grpc_streaming_transport",
        "//proto/session:service_streaming_cc_grpc",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/flags:flag",
        "@com_google_absl//absl/flags:parse",
        "@com_google_absl//absl/log",
    ],
)
