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

load("@graknlabs_bazel_distribution//packer:rules.bzl", "assemble_packer", "deploy_packer")

package(
    licenses = ["notice"],
)

exports_files(["config.json"])

assemble_packer(
    name = "assemble-oak-gcp-hello-world",
    config = ":config.json",
    files = {
        "//oak/server/loader:oak_runner": "oak_runner",
        "//examples/hello_world/config:config.bin": "config.bin",
    },
)

deploy_packer(
    name = "deploy-oak-gcp-hello-world",
    target = ":assemble-oak-gcp-hello-world",
)
