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
    name = "tensorflow.wasm",
    srcs = ["tensorflow.cc"],
    linkopts = [
        # Most of the link options are originated from the TFJS WASM backend:
        # https://github.com/tensorflow/tfjs/blob/09297d20dec2eef06150040a570499437757c919/tfjs-backend-wasm/src/cc/BUILD#L13-L24
        # It is not recommended to use "-s SINGLE_FILE=1" since a lot of the TensorFlow
        # libraries have `-lpthread -lm -ldl -lrt -ldl` link flags.
        # It is also not recommended to use "-s LINKABLE=1" parameter that disables dead code
        # elimination, since it would add a lot of unnecessary imports.
        # Emscripten options' documentation is in:
        # https://github.com/emscripten-core/emscripten/blob/1.39.5/src/settings.js
        "-s AUTO_ARCHIVE_INDEXES=0",  # Necessary to remove console spam.
        "-s DISABLE_EXCEPTION_CATCHING=1",
        "-s ERROR_ON_UNDEFINED_SYMBOLS=0",
        "-s EXIT_RUNTIME=0",
        "-s EXPORTED_FUNCTIONS='[\"_oak_main\"]'",
        "-s FILESYSTEM=0",
        "-s MALLOC=emmalloc",
        "-s STANDALONE_WASM=1",  # WASM file should run without JavaScript.
        "-s WARN_ON_UNDEFINED_SYMBOLS=0",
        "-s WASM=1",
    ],
    deps = [
        "//oak/module:defines",
        # TODO: Sort out inclusion of protobuf files
        # "//oak/proto:oak_api_cc_proto",
        "@org_tensorflow//tensorflow/lite:framework",
        "@org_tensorflow//tensorflow/lite/kernels:builtin_ops",
    ],
)
