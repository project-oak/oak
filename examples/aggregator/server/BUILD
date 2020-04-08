#
# Copyright 2020 The Project Oak Authors
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
load("//oak/server/loader:oak_docker.bzl", "oak_docker")

package(
    licenses = ["notice"],
)

oak_docker(
    name = "aggregator_image",
    application = "//examples/aggregator/config:config",
    ports = [
        "8080/tcp",  # Oak Application gRPC port.
    ],
)

container_image(
    name = "aggregator_backend_image",
    base = "@cc_image//image",
    files = [
        "//:target/release/aggregator_backend",
    ],
    ports = [
        "8888/tcp",  # Backend gRPC port.
    ],
)
