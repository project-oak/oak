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
    name = "client",
    srcs = [
        "src/Main.java",
    ],
    main_class = "com.google.oak.functions.examples.weather_lookup.client.Main",
    deps = [
        "//oak_functions/client/java:client",
        "//oak_functions/proto:invocation_java_proto",
        "//oak_functions/proto:invocation_proto",
        "@com_google_protobuf//:protobuf_java",
        "@com_google_protobuf//:protobuf_java_util",
        "@io_grpc_grpc_java//api",
        "@io_grpc_grpc_java//protobuf",
        "@io_grpc_grpc_java//stub",
    ],
)
