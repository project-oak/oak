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

load("@rules_java//java:defs.bzl", "java_test")

package(
    licenses = ["notice"],
)

java_test(
    name = "log_entry_verifier_test",
    srcs = ["LogEntryVerifierTest.java"],
    data = [
        "//oak_remote_attestation_verification/testdata:endorsement.json",
        "//oak_remote_attestation_verification/testdata:logentry.json",
        "//oak_remote_attestation_verification/testdata:rekor_public_key.pem",
    ],
    test_class = "com.google.oak.verification.LogEntryVerifierTest",
    deps = [
        "//java/src/main/java/com/google/oak/verification",
    ],
)

java_test(
    name = "main_verifier_test",
    srcs = ["MainVerifierTest.java"],
    data = [
        "//oak_remote_attestation_verification/testdata:endorsement.json",
        "//oak_remote_attestation_verification/testdata:logentry.json",
        "//oak_remote_attestation_verification/testdata:oak-development.pem",
        "//oak_remote_attestation_verification/testdata:rekor_public_key.pem",
    ],
    test_class = "com.google.oak.verification.MainVerifierTest",
    deps = [
        "//java/src/main/java/com/google/oak/verification",
        "//proto/attestation:endorsement_java_proto",
        "//proto/attestation:evidence_java_proto",
        "//proto/attestation:reference_value_java_proto",
    ],
)

java_test(
    name = "rekor_log_entry_test",
    srcs = ["RekorLogEntryTest.java"],
    data = ["//oak_remote_attestation_verification/testdata:logentry.json"],
    test_class = "com.google.oak.verification.RekorLogEntryTest",
    deps = [
        "//java/src/main/java/com/google/oak/verification",
    ],
)

java_test(
    name = "signature_verifier_test",
    srcs = ["SignatureVerifierTest.java"],
    data = [
        "//oak_remote_attestation_verification/testdata:endorsement.json",
        "//oak_remote_attestation_verification/testdata:endorsement.json.sig",
        "//oak_remote_attestation_verification/testdata:oak-development.pem",
    ],
    test_class = "com.google.oak.verification.SignatureVerifierTest",
    deps = [
        "//java/src/main/java/com/google/oak/verification",
    ],
)
