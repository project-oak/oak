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

load("@rules_cc//cc:cc_binary.bzl", "cc_binary")
load("@rules_rust//rust:defs.bzl", "rust_library")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_library(
    name = "attestation_verification_clock_test_rust",
    testonly = True,
    srcs = ["attestation_verification_clock_test_jni.rs"],
    deps = [
        "//java/src/main/java/com/google/oak/remote_attestation/jni:oak_jni_attestation_verification_clock",
        "//oak_attestation_verification_types",
        "//oak_time",
        "@oak_crates_index//:jni",
    ],
    alwayslink = 1,
)

cc_binary(
    name = "attestation_verification_clock_test_jni",
    testonly = True,
    linkshared = True,
    deps = [
        ":attestation_verification_clock_test_rust",
    ],
)
