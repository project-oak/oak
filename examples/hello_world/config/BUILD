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
load("@rules_cc//cc:defs.bzl", "cc_binary")

package(
    licenses = ["notice"],
)

exports_files(srcs = glob(["*.textproto"]))

genrule(
    name = "config",
    srcs = [
        ":config.textproto",
        "//examples:target/wasm32-unknown-unknown/release/hello_world.wasm",
    ],
    outs = ["config.bin"],
    cmd = "$(location //oak/common:app_config_serializer)" +
          " --textproto=$(location :config.textproto)" +
          " --modules=" +
              "app:$(location //examples:target/wasm32-unknown-unknown/release/hello_world.wasm)" + 
          " --output_file=$@",
    tools = ["//oak/common:app_config_serializer"],
)

genrule(
    name = "config_cpp",
    srcs = [
        ":config.textproto",
        "//examples/hello_world/module/cpp:hello_world.wasm",
    ],
    outs = ["config_cpp.bin"],
    cmd = "$(location //oak/common:app_config_serializer)" +
          " --textproto=$(location :config.textproto)" +
          " --modules=" +
              "app:$(location //examples/hello_world/module/cpp:hello_world.wasm)" + 
          " --output_file=$@",
    tools = ["//oak/common:app_config_serializer"],
)
