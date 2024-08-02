#
# Copyright 2024 The Project Oak Authors
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

# Controls the use of the +avx and +avx2 C compiler features.
constraint_setting(name = "avx")

constraint_value(
    name = "avx_ON",
    constraint_setting = "avx",
)

constraint_value(
    name = "avx_OFF",
    constraint_setting = "avx",
)

# Controls the use of the soft-float C compiler feature.
constraint_setting(name = "soft_float")

constraint_value(
    name = "soft_float_ON",
    constraint_setting = "soft_float",
)

constraint_value(
    name = "soft_float_OFF",
    constraint_setting = "soft_float",
)

constraint_setting(name = "code_model")

constraint_value(
    name = "code_model_LARGE",
    constraint_setting = "code_model",
)

constraint_value(
    name = "code_model_NORMAL",
    constraint_setting = "code_model",
)
