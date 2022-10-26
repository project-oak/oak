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
    "oak_copts",
)

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

#
# The `generated` directory is generated from the tflite-micro git:
# https://github.com/tensorflow/tflite-micro by:
# `python3 tensorflow/lite/micro/tools/project_generation/create_tflm_tree.py generated`
#
# The build target residing outside of the generated directory allows us to
# upgrade/downgrade (delete old then copy new) the generated directory cleanly.
#
cc_library(
    name = "tflm-generated",
    srcs = glob(
        ["generated/tensorflow/lite/**/*.cc"],
        exclude = [
            "generated/tensorflow/lite/micro/debug_log.cc",
        ],
    ),
    hdrs = glob([
        "generated/tensorflow/lite/**/*.h",
        "generated/third_party/flatbuffers/**/*.h",
        "generated/third_party/gemmlowp/**/*.h",
        "generated/third_party/ruy/**/*.h",
    ]),
    copts = oak_copts(),
    linkstatic = 1,
    deps = [
        # Use Oak DebugLog implementation
        "//cc/tflite_micro/oak:debug_log",
        # Use Oak pico libc
        "//cc/tflite_micro/oak/libc",
        # Use Oak pico libgcc
        "//cc/tflite_micro/oak/libgcc",
        # Use Oak pico libm that picks up complements of Oak Restricted Kernel libm.rs
        "//cc/tflite_micro/oak/libm:oak_kernel_complements",
    ],
)
