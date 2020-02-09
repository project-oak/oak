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

load("@io_bazel_rules_docker//container:container.bzl", "container_image")
load("@rules_cc//cc:defs.bzl", "cc_binary")

package(
    licenses = ["notice"],
)

cc_binary(
    name = "client",
    srcs = ["hello_world.cc"],
    deps = [
        "//examples/hello_world/proto:hello_world_cc_grpc",
        "//oak/client:application_client",
        "@com_github_grpc_grpc//:grpc++",
        "@com_google_absl//absl/flags:flag",
        "@com_google_absl//absl/flags:parse",
        "@com_google_asylo//asylo/util:logging",
    ],
)

# TODO: Create a new Bazel rule `oak_application_server_docker`, that encapsulates this logic.
container_image(
    name = "client_docker",
    base = "//oak/server/asylo:oak_app_docker",
    entrypoint = [
        "./oak_app_host_loader",
        "--enclave_path=oak_enclave_debug.so",
        "--module=hello_world.wasm",
        "--grpc_port=8080",
    ],
    files = [
        "//examples:target/wasm32-unknown-unknown/release/hello_world.wasm",
    ],
    ports = [
        "8080/tcp",  # Oak Application gRPC port.
    ],
    repository = "gcr.io/oak-ci",
)
