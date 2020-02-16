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

load("//oak/common:app_config.bzl", "serialized_config")

package(
    licenses = ["notice"],
)

exports_files(srcs = glob(["*.textproto"]))

serialized_config(
    name = "config",
    modules = {
        "frontend-config": "//:target/wasm32-unknown-unknown/release/abitest_0_frontend.wasm",
        "backend-config": "//:target/wasm32-unknown-unknown/release/abitest_1_backend.wasm",
    },
    textproto = ":config.textproto",
)
