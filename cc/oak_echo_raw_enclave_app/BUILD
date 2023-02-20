#
# Copyright 2023 The Project Oak Authors
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

package(
    licenses = ["notice"],
)

cc_binary(
    name = "oak_echo_raw_enclave_app",
    srcs = ["main.cc"],
    copts = [
        "-nostdlib",
        "-ffreestanding",
    ],
    features = ["fully_static_link"],
    linkopts = [
        "-nostdlib",
        "-Wl,-zmax-page-size=0x200000",
    ],
    target_compatible_with = [
        "@platforms//cpu:x86_64",
        "//:os_oak",
    ],
    deps = ["//third_party/newlib"],
)
