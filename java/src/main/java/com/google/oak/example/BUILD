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
    name = "example",
    srcs = glob(["*.java"]),
    deps = [
        "//java/proto/example:secure_service_java_grpc",
        "//java/proto/example:secure_service_java_proto",
        "//java/src/main/java/com/google/oak/crypto/hpke",
        "//java/src/main/java/com/google/oak/server",
        "//java/src/main/java/com/google/oak/util",
        "//proto/session/v1:service_streaming_java_proto",
        "@io_grpc_grpc_java//stub",
    ],
)
