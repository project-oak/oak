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

"""Aggregates TFLM-on-Oak build copts and provides tflite model conversion macro."""

def oak_copts():
    return [
        "-std=c++11",
        "-fno-rtti",
        "-fno-exceptions",
        "-fno-threadsafe-statics",
        "-fno-stack-protector",
        "-fno-use-cxa-atexit",
        "-fno-unwind-tables",
        "-ffunction-sections",
        "-fdata-sections",
        "-fmessage-length=0",
        "-Wall",
        "-Werror",
        "-Wdouble-promotion",
        "-Wshadow",
        "-Wunused-variable",
        "-Wunused-function",
        "-Wswitch",
        "-Wvla",
        "-Wextra",
        "-Wmissing-field-initializers",
        "-Wstrict-aliasing",
        "-Wno-sign-compare",
        "-Wno-unused-parameter",
        "-Wno-ignored-attributes",
        "-Wnon-virtual-dtor",
        "-DFARMHASH_NO_CXX_STRING",
        "-DTF_LITE_STATIC_MEMORY",
        "-Icc/tflite_micro/include",
        "-Ithird_party/tflite-micro",
        "-Ithird_party/flatbuffers/include",
        "-Ithird_party/gemmlowp",
        "-Ithird_party/ruy",
    ] + select({
        "//cc/tflite_micro:no_sse": [],
        "//conditions:default": ["-msse4.2"],
    }) + select({
        "//cc/tflite_micro:no_opt": ["-O0"],
        "//conditions:default": ["-O2", "-DNDEBUG"],
    })

def generate_cc_arrays(name, src, out, visibility = None):
    native.genrule(
        name = name,
        srcs = [
            src,
        ],
        outs = [
            out,
        ],
        cmd = "python3 $(location //cc/tflite_micro/tools:generate_cc_arrays) $@ $<",
        tools = ["//cc/tflite_micro/tools:generate_cc_arrays"],
        visibility = visibility,
    )
