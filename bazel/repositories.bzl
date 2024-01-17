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
"""Functions to load Oak dependencies."""

load("//bazel/tools/umoci:umoci_toolchain.bzl", "register_umoci_toolchain")

# buildifier: disable=unnamed-macro
def oak_repositories(oak_workspace_name = None):
    """Downloads dependencies and registers toolchains used by Oak rules."""
    register_umoci_toolchain(name = "umoci_toolchain", oak_workspace_name = oak_workspace_name)
