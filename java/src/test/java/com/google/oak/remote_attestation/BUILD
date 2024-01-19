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
    name = "amd_attestation_verifier_test",
    srcs = ["AmdAttestationVerifierTest.java"],
    test_class = "com.google.oak.remote_attestation.AmdAttestationVerifierTest",
    deps = [
        "//java/src/main/java/com/google/oak/remote_attestation:amd_attestation_verifier",
        "//java/src/main/java/com/google/oak/util",
        "//proto/attestation:verification_java_proto",
    ],
)
