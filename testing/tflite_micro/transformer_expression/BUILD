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
    "//cc/tflite_micro:build_defs.bzl",
    "generate_cc_arrays",
    "oak_copts",
)

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

generate_cc_arrays(
    name = "generated_transformer_expression_model_cc",
    src = "transformer_expression.tflite",
    out = "transformer_expression_model_data.cc",
)

generate_cc_arrays(
    name = "generated_transformer_expression_model_hdr",
    src = "transformer_expression.tflite",
    out = "transformer_expression_model_data.h",
)

cc_library(
    name = "transformer_expression_model",
    srcs = [
        ":generated_transformer_expression_model_cc",
    ],
    hdrs = [
        ":generated_transformer_expression_model_hdr",
    ],
)

cc_library(
    name = "testdata",
    hdrs = ["testdata.c"],
)

# Freestanding executable running on host for debugging
# i.e. model input, output, ops and pipeline via gdb/lldb.
cc_binary(
    name = "transformer_expression",
    srcs = ["main.cc"],
    copts = oak_copts(),
    linkopts = ["-nostdlib"],
    deps = [
        ":testdata",
        ":transformer_expression_model",
        "//cc/tflite_micro:hdrs",
        "//cc/tflite_micro:tflite_micro_generic",
        "//testing/tflite_micro:start_file",
    ],
)
