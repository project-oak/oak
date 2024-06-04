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
Load the jemalloc repository needed for tikv-jemallocator crate to build.
"""

load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")

def jemalloc_repository():
    # Build jemalloc with bazel, so that we can provide it to the tikv-jemallocator build script.
    git_repository(
        name = "jemalloc",
        build_file = "@oak//bazel:jemalloc.BUILD",
        # jemalloc pointer for tikv-jemalloc-sys submodule pointer at 0.5.3
        commit = "e13ca993e8ccb9ba9847cc330696e02839f328f7",

        # Fix an issue when building jemalloc with gcc 10.3 (which is the version we
        # currently use due to the aspect_gcc target)
        # There's a target in the Makefile that uses the -MM flag, and
        # when it does that, it doesn't include the $(CFLAGS).
        # This results in __GNUC_PREREQ not being defined, which causes compiler
        # failures.
        # As a workaround, we patch that line in the Makefile.in to include the CFLAGS.
        # TODO: b/341166977 Remove this when we can.
        patch_cmds = ["sed -i '481s/-MM/$(CFLAGS) -MM/' Makefile.in"],
        remote = "https://github.com/tikv/jemalloc",
    )
