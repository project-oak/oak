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

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

#
# Complements of libm.rs for Oak Restricted Kernel.
#
# Target those math functions that cannot be easily implemented in Oak
# Restricted Kernel under no_std constrain.
#
# TODO: Remove unnessary functions once there are proper Rust impl. in place.
#
cc_library(
    name = "oak_kernel_complements",
    srcs = [
        # Rust frexp: pub fn frexp(x: f64) -> (f64, i32)
        # has different signature from C/C++.
        "frexp.c",
    ],
)
