#
# Copyright 2019 The Project Oak Authors
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

load("@rules_cc//cc:defs.bzl", "cc_binary")

package(
    licenses = ["notice"],
)

cc_binary(
    name = "client",
    srcs = ["running_average.cc"],
    deps = [
        "//examples/running_average/proto:running_average_cc_grpc",
        "//oak/client:application_client",
        "//oak/client:manager_client",
        "//oak/common:nonce_generator",
        "//oak/common:utils",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/flags:flag",
        "@com_google_absl//absl/flags:parse",
        "@com_google_absl//absl/memory",
        "@com_google_asylo//asylo/util:logging",
    ],
)

genrule(
    name = "client_config",
    srcs = ["//examples:target/wasm32-unknown-unknown/release/running_average.wasm"],
    outs = ["client_config.bin"],
    cmd = "$(location //oak/common:app_config_serializer)" +
          " --module=$<" +
          " --logging" +
          " --storage_address=127.0.0.1:7867" +
          " --grpc_port=8080" +
          " --output_file=$@",
    tools = ["//oak/common:app_config_serializer"],
)
