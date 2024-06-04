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
#
"""
Load all the crate repositories created by create_oak_crate_repoitories.

Usage:

load("//bazel/crates:repositories.bzl", "create_oak_crate_repositories")

create_oak_crate_repositories()

load("//bazel/crates:crates.bzl", "load_oak_crate_repositories")

load_oak_crate_repositories()

"""

load("@oak_crates_index//:defs.bzl", "crate_repositories")
load("@oak_no_std_crates_index//:defs.bzl", no_std_crate_repositories = "crate_repositories")

def load_oak_crate_repositories():
    crate_repositories()
    no_std_crate_repositories()
