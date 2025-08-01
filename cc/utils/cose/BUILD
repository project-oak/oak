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

load("@rules_cc//cc:cc_library.bzl", "cc_library")
load("@rules_cc//cc:cc_test.bzl", "cc_test")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

# Libraries

cc_library(
    name = "cose",
    srcs = ["cose.cc"],
    hdrs = ["cose.h"],
    deps = [
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
        "@libcppbor",
    ],
)

cc_library(
    name = "cwt",
    srcs = ["cwt.cc"],
    hdrs = ["cwt.h"],
    deps = [
        ":cose",
        "@com_google_absl//absl/status",
        "@com_google_absl//absl/status:statusor",
        "@com_google_absl//absl/strings",
        "@libcppbor",
    ],
)

# Tests

cc_test(
    name = "cose_test",
    size = "small",
    srcs = ["cose_test.cc"],
    deps = [
        ":cose",
        "@com_google_googletest//:gtest_main",
    ],
)

cc_test(
    name = "cwt_test",
    size = "small",
    srcs = ["cwt_test.cc"],
    data = ["//oak_attestation_verification/testdata:milan_oc_staging_attestation"],
    deps = [
        ":cwt",
        "//proto/attestation:evidence_cc_proto",
        "@com_google_absl//absl/strings",
        "@com_google_googletest//:gtest_main",
    ],
)
