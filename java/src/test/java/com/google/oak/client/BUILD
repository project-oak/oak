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
    name = "client_test",
    srcs = glob(["*.java"]),
    test_class = "com.google.oak.client.OakClientTest",
    deps = [
        "//java/src/main/java/com/google/oak/client",
        "//java/src/main/java/com/google/oak/crypto:server_encryptor",
        "//java/src/main/java/com/google/oak/crypto/hpke",
        "//java/src/main/java/com/google/oak/remote_attestation:insecure_attestation_verifier",
        "//java/src/main/java/com/google/oak/transport",
        "//java/src/main/java/com/google/oak/util",
        "//oak_crypto/proto/v1:crypto_java_proto",
        "//oak_remote_attestation/proto/v1:messages_java_proto",
        "@com_google_protobuf//:protobuf_javalite",
    ],
)
