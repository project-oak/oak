#
# Copyright 2019 The Project Oak Authors
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

"""Fuzz-related definitions for Oak testing."""

# Inspired by https://github.com/grpc/grpc/blob/618a3f561d4a93f263cca23abad086ed8f4d5e86/test/core/util/grpc_fuzzer.bzl.
def oak_fuzzer(name, srcs = [], deps = [], **kwargs):
    native.cc_binary(
        name = name,
        srcs = srcs,
        deps = deps,
        **kwargs
    )
