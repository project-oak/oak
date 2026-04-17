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
load("@rules_java//java:defs.bzl", "java_test")
load("@rules_kotlin//kotlin:jvm.bzl", "kt_jvm_library")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

kt_jvm_library(
    name = "AttestationVerificationClockTestLib",
    testonly = True,
    srcs = ["AttestationVerificationClockTest.kt"],
    deps = [
        "//java/src/main/java/com/google/oak/remote_attestation:attestation_verification_clock",
        "@maven//:junit_junit",
        "@maven//:org_jetbrains_kotlin_kotlin_test",
    ],
)

# We structure the test this way because kt_jvm_test doesn't handle JNI deps very easily.
java_test(
    name = "AttestationVerificationClockTest",
    test_class = "com.google.oak.remote_attestation.AttestationVerificationClockTest",
    runtime_deps = [
        ":AttestationVerificationClockTestLib",
        "//java/src/test/java/com/google/oak/remote_attestation/jni:attestation_verification_clock_test_jni",
    ],
)
