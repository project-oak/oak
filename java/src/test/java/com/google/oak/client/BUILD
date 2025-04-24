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
load("@rules_kotlin//kotlin:jvm.bzl", "kt_jvm_test")

package(
    licenses = ["notice"],
)

java_test(
    name = "client_test",
    srcs = ["OakClientTest.java"],
    test_class = "com.google.oak.client.OakClientTest",
    deps = [
        "//java/src/main/java/com/google/oak/client",
        "//java/src/main/java/com/google/oak/crypto:server_encryptor",
        "//java/src/main/java/com/google/oak/crypto/hpke",
        "//java/src/main/java/com/google/oak/remote_attestation:attestation_verifier",
        "//java/src/main/java/com/google/oak/transport",
        "//java/src/main/java/com/google/oak/util",
        "//proto/attestation:endorsement_java_proto",
        "//proto/attestation:evidence_java_proto",
        "//proto/attestation:verification_java_proto",
        "//proto/crypto:crypto_java_proto",
        "//proto/session:messages_java_proto",
        "@com_google_protobuf//:protobuf_javalite",
        "@maven//:junit_junit",
    ],
)

kt_jvm_test(
    name = "session_client_test",
    srcs = [
        "OakSessionClientTest.kt",
    ],
    # Kotlin unit test doesn't set the library path inside the runfiles dir, so some creative flag
    # manipulation is necessary.
    jvm_flags = ["-Djava.library.path=$(rlocation oak/java/src/main/java/com/google/oak/session/jni)"],
    test_class = "com.google.oak.client.OakSessionClientTest",
    deps = [
        "//java/src/main/java/com/google/oak/client:session_client",
        "//java/src/main/java/com/google/oak/session:server_session",
        "//java/src/main/java/com/google/oak/session:session_config_builder",
        "//java/src/main/java/com/google/oak/transport:grpc_session_v1_client_transport",
        "//java/src/main/java/com/google/oak/transport:session_transport",
        "//proto/services:session_v1_service_java_grpc",
        "//proto/session:session_java_proto",
        "@com_google_protobuf//:protobuf_java",
        "@io_grpc_grpc_java//core",
        "@io_grpc_grpc_java//inprocess",
        "@io_grpc_grpc_java//stub",
        "@maven//:junit_junit",
        "@maven//:org_jetbrains_kotlin_kotlin_test",
        "@maven//:org_jetbrains_kotlinx_kotlinx_coroutines_core",
        "@maven//:org_jetbrains_kotlinx_kotlinx_coroutines_test",
    ],
)
