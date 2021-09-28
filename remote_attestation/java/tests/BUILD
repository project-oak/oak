#
# Copyright 2021 The Project Oak Authors
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
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

java_test(
    name = "message_test",
    srcs = [
        "com/google/oak/remote_attestation/MessageTest.java",
    ],
    test_class = "com.google.oak.remote_attestation.MessageTest",
    deps = [
        "//remote_attestation/java:remote_attestation",
    ],
)

java_test(
    name = "key_negotiator_test",
    srcs = [
        "com/google/oak/remote_attestation/KeyNegotiatorTest.java",
    ],
    test_class = "com.google.oak.remote_attestation.KeyNegotiatorTest",
    deps = [
        "//remote_attestation/java:remote_attestation",
    ],
)

java_test(
    name = "client_handshaker_test",
    srcs = [
        "com/google/oak/remote_attestation/ClientHandshakerTest.java",
    ],
    test_class = "com.google.oak.remote_attestation.ClientHandshakerTest",
    deps = [
        "//remote_attestation/java:remote_attestation",
    ],
)
