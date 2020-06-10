#
# Copyright 2018 The Project Oak Authors
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

package(
    default_visibility = [
        "//examples:__subpackages__",
        "//oak/server:__subpackages__",
    ],
    licenses = ["notice"],
)

container_image(
    name = "oak_docker",
    base = "@cc_image//image",
    files = [
        "target/x86_64-unknown-linux-musl/release/oak_loader",
    ],
    ports = [
        "8080/tcp",  # Oak Application gRPC port.
    ],
    repository = "gcr.io/oak-ci",
)
