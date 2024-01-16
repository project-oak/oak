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

load("@rules_java//java:defs.bzl", "java_test")

package(
    licenses = ["notice"],
)

java_test(
    name = "grpc_streaming_transport_test",
    srcs = ["GrpcStreamingTransportTest.java"],
    test_class = "com.google.oak.transport.GrpcStreamingTransportTest",
    deps = [
        "//java/src/main/java/com/google/oak/transport:grpc_streaming_transport",
        "//java/src/main/java/com/google/oak/util",
        "//oak_crypto/proto/v1:crypto_java_proto",
        "//proto/session:messages_java_proto",
        "//proto/session:service_streaming_java_grpc",
        "//proto/session:service_streaming_java_proto",
        "@com_google_protobuf//:protobuf_javalite",
        "@io_grpc_grpc_java//api",
        "@io_grpc_grpc_java//core:inprocess",
        "@io_grpc_grpc_java//stub",
        "@io_grpc_grpc_java//testing",
        "@org_mockito_mockito_core",
    ],
)
