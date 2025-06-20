#
# Copyright 2022 The Project Oak Authors
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

load("@rules_kotlin//kotlin:jvm.bzl", "kt_jvm_test")

package(
    licenses = ["notice"],
)

kt_jvm_test(
    name = "log_entry_verifier_test",
    srcs = ["LogEntryVerifierTest.kt"],
    data = ["//oak_attestation_verification/testdata:endorsement"],
    test_class = "com.google.oak.verification.LogEntryVerifierTest",
    deps = [
        "//java/src/main/java/com/google/oak/verification",
        "@junit_junit",
        "@rules_kotlin//kotlin/compiler:kotlin-test",
    ],
)

kt_jvm_test(
    name = "rekor_log_entry_test",
    srcs = ["RekorLogEntryTest.kt"],
    data = ["//oak_attestation_verification/testdata:endorsement"],
    test_class = "com.google.oak.verification.RekorLogEntryTest",
    deps = [
        "//java/src/main/java/com/google/oak/verification",
        "@junit_junit",
        "@rules_kotlin//kotlin/compiler:kotlin-test",
    ],
)

kt_jvm_test(
    name = "signature_verifier_test",
    srcs = ["SignatureVerifierTest.kt"],
    data = ["//oak_attestation_verification/testdata:endorsement"],
    test_class = "com.google.oak.verification.SignatureVerifierTest",
    deps = [
        "//java/src/main/java/com/google/oak/verification",
        "@junit_junit",
        "@rules_kotlin//kotlin/compiler:kotlin-test",
    ],
)
