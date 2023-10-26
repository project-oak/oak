#
# Copyright 2023 The Project Oak Authors
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
    name = "decryption_result",
    srcs = [
        "DecryptionResult.java",
    ],
)

java_library(
    name = "client_encryptor",
    srcs = [
        "ClientEncryptor.java",
    ],
    deps = [
        ":decryption_result",
        "//java/src/main/java/com/google/oak/crypto/hpke",
        "//java/src/main/java/com/google/oak/util",
        "//oak_crypto/proto/v1:crypto_java_proto",
        "@com_google_protobuf//:protobuf_javalite",
        "@com_google_protobuf//java/core",
    ],
)

java_library(
    name = "server_encryptor",
    srcs = [
        "ServerEncryptor.java",
    ],
    deps = [
        ":decryption_result",
        "//java/src/main/java/com/google/oak/crypto/hpke",
        "//java/src/main/java/com/google/oak/util",
        "//oak_crypto/proto/v1:crypto_java_proto",
        "@com_google_protobuf//:protobuf_javalite",
        "@com_google_protobuf//java/core",
    ],
)
