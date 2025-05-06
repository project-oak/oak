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
    licenses = ["notice"],
)

kt_jvm_library(
    name = "stream_observer_session_client_test_lib",
    testonly = True,
    srcs = ["StreamObserverSessionClientTest.kt"],
    deps = [
        "//java/src/main/java/com/google/oak/client/grpc:stream_observer_session_client",
        "//java/src/main/java/com/google/oak/session:client_session",
        "//java/src/main/java/com/google/oak/session:server_session",
        "//java/src/main/java/com/google/oak/session:session_config_builder",
        "//proto/session:session_java_proto",
        "@com_google_protobuf//:protobuf_java",
        "@io_grpc_grpc_java//stub",
        "@javax_inject_javax_inject",
        "@maven//:junit_junit",
        "@org_mockito_kotlin_mockito_kotlin",
    ],
)

# We structure the test this way because kt_jvm_test doesn't handle JNI deps very easily.
java_test(
    name = "StreamObserverSessionClientTest",
    test_class = "com.google.oak.client.grpc.StreamObserverSessionClientTest",
    runtime_deps = [
        ":stream_observer_session_client_test_lib",
        "//java/src/main/java/com/google/oak/session/jni/jvm:oak_client_session_jni",
        "//java/src/main/java/com/google/oak/session/jni/jvm:oak_server_session_jni",
    ],
)
