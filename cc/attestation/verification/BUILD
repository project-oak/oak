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

load("@rules_cc//cc:cc_library.bzl", "cc_library")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

cc_library(
    name = "attestation_verifier",
    hdrs = ["attestation_verifier.h"],
    deps = [
        "//proto/attestation:endorsement_cc_proto",
        "//proto/attestation:evidence_cc_proto",
        "//proto/attestation:verification_cc_proto",
        "@com_google_absl//absl/status:statusor",
    ],
)

cc_library(
    name = "insecure_attestation_verifier",
    srcs = ["insecure_attestation_verifier.cc"],
    hdrs = ["insecure_attestation_verifier.h"],
    deps = [
        ":attestation_verifier",
        ":utils",
        "//proto/attestation:endorsement_cc_proto",
        "//proto/attestation:evidence_cc_proto",
        "//proto/attestation:verification_cc_proto",
        "@com_google_absl//absl/status:statusor",
    ],
)

cc_library(
    name = "utils",
    srcs = ["utils.cc"],
    hdrs = ["utils.h"],
    deps = [
        "//cc/utils/cose:cwt",
        "//proto/attestation:eventlog_cc_proto",
        "//proto/attestation:evidence_cc_proto",
        "//proto/attestation:verification_cc_proto",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
    ],
)
