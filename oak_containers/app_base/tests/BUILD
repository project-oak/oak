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

load("@rules_python//python:defs.bzl", "py_test")
load("//oak_containers/app_base:defs.bzl", "app_bundle", "oak_app_config")

package(
    default_visibility = ["//visibility:private"],
    licenses = ["notice"],
)

# Dummy binary for bundle testing
genrule(
    name = "test_binary_gen",
    outs = ["test_binary"],
    cmd = "touch $@",
)

oak_app_config(
    name = "test_config_json",
    args = [
        "/usr/local/bin/test_binary",
        "--arg1",
        "val1",
    ],
    env = {
        "MY_ENV": "test",
        "HOME": "/overridden_home",
    },
)

oak_app_config(
    name = "custom_root_config_json",
    args = ["/bin/true"],
    root_path = "custom_root",
)

app_bundle(
    name = "test_bundle",
    args = [
        "--arg1",
        "val1",
    ],
    binary = ":test_binary_gen",
    env = {"MY_ENV": "test"},
)

py_test(
    name = "test_config",
    srcs = ["test_config.py"],
    data = [
        ":custom_root_config_json",
        ":test_config_json",
    ],
    env = {
        "CONFIG_JSON_PATH": "$(location :test_config_json)",
        "CUSTOM_ROOT_CONFIG_PATH": "$(location :custom_root_config_json)",
    },
    deps = [],
)
