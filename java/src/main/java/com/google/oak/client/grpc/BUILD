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

load("@rules_kotlin//kotlin:android.bzl", "kt_android_library")
load("@rules_kotlin//kotlin:jvm.bzl", "kt_jvm_library")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

kt_jvm_library(
    name = "stream_observer_session_client",
    srcs = [
        "StreamObserverSessionClient.kt",
    ],
    deps = [
        "//java/src/main/java/com/google/oak/session:client_session",
        "//java/src/main/java/com/google/oak/session:exception",
        "//java/src/main/java/com/google/oak/session:session_config_builder",
        "//proto/session:session_java_proto",
        "@com_google_protobuf//java/core",
        "@io_grpc_grpc_java//stub",
        "@javax_inject_javax_inject",
    ],
)

kt_android_library(
    name = "stream_observer_session_client_android",
    srcs = [
        "StreamObserverSessionClient.kt",
    ],
    deps = [
        "//java/src/main/java/com/google/oak/session:client_session_android",
        "//java/src/main/java/com/google/oak/session:exception_android",
        "//java/src/main/java/com/google/oak/session:session_config_builder_android",
        "//proto/session:session_java_proto",
        "@com_google_protobuf//java/lite",
        "@io_grpc_grpc_java//stub",
        "@javax_inject_javax_inject",
    ],
)
