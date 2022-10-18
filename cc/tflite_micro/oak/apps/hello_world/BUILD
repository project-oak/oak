#
# Copyright 2022 The Project Oak Authors
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

load(
    "//cc/tflite_micro/oak:build_def.bzl",
    "generate_cc_arrays",
    "oak_copts",
)

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

generate_cc_arrays(
    name = "generated_hello_world_model_cc",
    src = "hello_world.tflite",
    out = "hello_world_model_data.cc",
)

generate_cc_arrays(
    name = "generated_hello_world_model_hdr",
    src = "hello_world.tflite",
    out = "hello_world_model_data.h",
)

cc_library(
    name = "hello_world_model",
    srcs = [
        ":generated_hello_world_model_cc",
    ],
    hdrs = [
        ":generated_hello_world_model_hdr",
    ],
)

# Linked by oak_tensorflow_service and the self-contained binary below.
cc_library(
    name = "lib",
    srcs = ["hello_world.cc"],
    deps = [
        ":hello_world_model",
        "//cc/tflite_micro/generated:tflm",
        "//cc/tflite_micro/oak:hdrs",
    ],
    linkstatic = 1,
    alwayslink = 1,
    copts = oak_copts(),
    linkopts = ["-nostdlib"],
)

cc_binary(
    srcs = ["main.cc"],
    name = "hello_world",
    deps = [
        ":lib",
        "//cc/tflite_micro/oak:hdrs",
        "//cc/tflite_micro/oak/apps:start_file",
    ],
    copts = oak_copts(),
)