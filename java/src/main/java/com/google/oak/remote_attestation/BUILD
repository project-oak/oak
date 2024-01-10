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

load("@rules_java//java:defs.bzl", "java_library")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

java_library(
    name = "attestation_verifier",
    srcs = ["AttestationVerifier.java"],
    deps = [
        "//java/src/main/java/com/google/oak/util",
        "//proto/session:messages_java_proto",
    ],
)

java_library(
    name = "attestation_verifier_android",
    srcs = ["AttestationVerifier.java"],
    deps = [
        "//java/src/main/java/com/google/oak/util",
        "//proto/session:messages_java_proto",
    ],
)

java_library(
    name = "amd_attestation_verifier",
    srcs = ["AmdAttestationVerifier.java"],
    deps = [
        ":attestation_verifier",
        "//java/src/main/java/com/google/oak/util",
        "//proto/session:messages_java_proto",
    ],
)

java_library(
    name = "insecure_attestation_verifier",
    srcs = ["InsecureAttestationVerifier.java"],
    deps = [
        ":attestation_verifier",
        "//java/src/main/java/com/google/oak/util",
        "//proto/session:messages_java_proto",
    ],
)

java_library(
    name = "insecure_attestation_verifier_android",
    srcs = ["InsecureAttestationVerifier.java"],
    deps = [
        ":attestation_verifier_android",
        "//java/src/main/java/com/google/oak/util",
        "//proto/session:messages_java_proto",
    ],
)
