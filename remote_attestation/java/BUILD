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

load("@rules_java//java:defs.bzl", "java_library")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

java_library(
    name = "remote_attestation",
    srcs = [
        "src/com/google/oak/remote_attestation/AttestationStateMachine.java",
        "src/com/google/oak/remote_attestation/crypto/AeadEncryptor.java",
        "src/com/google/oak/remote_attestation/crypto/KeyNegotiator.java",
    ],
    deps = [
        "//remote_attestation/proto:remote_attestation_java_grpc",
        "//remote_attestation/proto:remote_attestation_java_proto",
        "//remote_attestation/proto:remote_attestation_proto",
        "@com_google_guava_guava",
        "@com_google_protobuf//:protobuf_java",
    ],
)

java_library(
    name = "remote_attestation_tink",
    srcs = [
        "src/com/google/oak/remote_attestation/AttestationStateMachine.java",
        "src/com/google/oak/remote_attestation/crypto/tink/AeadEncryptor.java",
        "src/com/google/oak/remote_attestation/crypto/tink/KeyNegotiator.java",
    ],
    deps = [
        "//remote_attestation/proto:remote_attestation_java_grpc",
        "//remote_attestation/proto:remote_attestation_java_proto",
        "//remote_attestation/proto:remote_attestation_proto",
        "@com_google_guava_guava",
        "@com_google_protobuf//:protobuf_java",
        "@tink_java//src/main/java/com/google/crypto/tink/subtle:aes_gcm_jce",
        "@tink_java//src/main/java/com/google/crypto/tink/subtle:x25519",
    ],
)
