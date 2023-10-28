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
    "//cc:build_defs.bzl",
    "cc_static_library",
)
load(
    "//cc/tflite_micro:build_defs.bzl",
    "oak_copts",
)

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

cc_library(
    name = "tflite_micro_core",
    srcs = [
        "//third_party/tflite-micro:srcs",
    ],
    hdrs = [
        "//third_party/flatbuffers:hdrs",
        "//third_party/gemmlowp:hdrs",
        "//third_party/ruy:hdrs",
        "//third_party/tflite-micro:hdrs",
    ],
    copts = oak_copts(),
    linkstatic = 1,
    deps = [
        # Use Oak DebugLog implementation
        ":debug_log",
        # Use Oak pico libc
        "//cc/libc",
        # Use Oak pico libgcc
        "//cc/libgcc",
        # Use Oak pico libm that picks up complements of Oak Restricted Kernel libm.rs
        "//cc/libm:oak_kernel_complements",
    ],
)

# Shared target used by both Linux freestanding binary
# and Oak TensorFlow enclave to run generic tflite models.
cc_library(
    name = "tflite_micro_generic",
    srcs = ["tflite_micro.cc"],
    copts = oak_copts(),
    linkstatic = 1,
    deps = [
        ":hdrs",
        ":tflite_micro_core",
    ],
)

# Fully static library linked by oak_tensorflow_service.
cc_static_library(
    name = "tflite_micro",
    deps = [":tflite_micro_generic"],
)

cc_library(
    name = "debug_log",
    srcs = [
        "debug_log.cc",
    ],
    copts = oak_copts(),
    deps = [":hdrs"],
)

cc_library(
    name = "hdrs",
    hdrs = [
        "tflite_micro.h",
        "//third_party/tflite-micro:hdrs",
    ],
    copts = oak_copts(),
)

# --define no_sse=1 to build tflite w/o streaming SIMD instructions.
# It would also use non-optimized Oak pico libc {str|mem}xxx functions.
config_setting(
    name = "no_sse",
    values = {
        "define": "no_sse=1",
    },
)

# --define no_opt=1 to disable compiler optimizations (-O0)
# rather than taking the default full optimizaiton (-O3)
config_setting(
    name = "no_opt",
    values = {
        "define": "no_opt=1",
    },
)
