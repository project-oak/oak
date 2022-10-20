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
    "//cc/tflite_micro/oak:build_defs.bzl",
    "generate_cc_arrays",
    "oak_copts",
)

load(
    "//cc:build_defs.bzl",
    "cc_static_library",
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

# Can be used i.e. link to custom output handlers for testing
# where tensor outputs are checked and asserted.
config_setting(
    name = "use_custom_output",
    values = {
        "define": "use_custom_output=1",
    },
)

cc_library(
    name = "hello_world",
    srcs = ["hello_world.cc"] + select({
        ":use_custom_output": [],
        "//conditions:default": ["output_handler.cc"],
    }),
    hdrs = ["output_handler.h"],
    deps = [
        ":hello_world_model",
        "//cc/tflite_micro/generated:tflm",
        "//cc/tflite_micro/oak:hdrs",
    ],
    linkstatic = 1,
    copts = oak_copts() + [
        "-Icc/tflite_micro/oak/apps/hello_world",
    ],
    linkopts = ["-nostdlib"],
)

# Fully static library linked by oak_tensorflow_service.
cc_static_library(
    name = "hello_world_app",
    deps = [":hello_world"],
)

# Freestanding executable running on host for debugging
# i.e. model input, output, ops and pipeline via gdb/lldb.
cc_binary(
    srcs = ["main.cc"],
    name = "hello_world_freestanding_bin",
    deps = [
        ":hello_world",
        "//cc/tflite_micro/oak:hdrs",
        "//cc/tflite_micro/oak/apps:start_file",
    ],
    copts = oak_copts(),
)
