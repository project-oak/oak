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

load("@rules_java//java:defs.bzl", "java_binary")

package(
    licenses = ["notice"],
)

java_binary(
    name = "grpc_attestation_client",
    srcs = [
        "com/google/oak/grpc_attestation_client/AeadEncryptor.java",
        "com/google/oak/grpc_attestation_client/AttestationClient.java",
        "com/google/oak/grpc_attestation_client/KeyNegotiator.java",
        "com/google/oak/grpc_attestation_client/Main.java",
    ],
    main_class = "com.google.oak.grpc_attestation_client.Main",
    runtime_deps = [
        "@io_grpc_grpc_java//netty",
    ],
    deps = [
        "//experimental/grpc_attestation/proto:grpc_attestation_java_grpc",
        "//experimental/grpc_attestation/proto:grpc_attestation_java_proto",
        "//experimental/grpc_attestation/proto:grpc_attestation_proto",
        "@com_google_protobuf//:protobuf_java",
        "@com_google_protobuf//:protobuf_java_util",
        "@io_grpc_grpc_java//api",
        "@io_grpc_grpc_java//protobuf",
        "@io_grpc_grpc_java//stub",
        "@tink_java//src/main/java/com/google/crypto/tink/subtle:aes_gcm_jce",
        "@tink_java//src/main/java/com/google/crypto/tink/subtle:x25519",
    ],
)
