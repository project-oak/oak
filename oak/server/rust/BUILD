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

load("@io_bazel_rules_rust//rust:rust.bzl", "rust_library")
load("@rules_cc//cc:defs.bzl", "cc_library")

package(
    licenses = ["notice"],
)

rust_library(
    name = "oak_runtime",
    srcs = glob(["src/**/*.rs"]),
    crate_type = "staticlib",
    edition = "2018",
)

# Strip unnecessary binary objects from the generated static library archive. It seems to contain
# mostly references to compiler intrinsics that are not needed and cannot be linked to the final
# enclave file.
# - The Asylo build creates a `.so` dynamic library to run in the enclave.
# - Because it's linking a `.so`, all static libraries dependencies are linked with the
#   `-whole-archive` option, which pulls in all the object files in the static library regardless of
#   whether they're used or not.
# - The static library built from the Rust code includes some small objects implementing compiler
#   intrinsics, including `__divxc3()` in a file `divxc3.o`.
# - This object file has undefined references to `fmaxl`, `logbl` and `scalbnl` (intrinsics for
#   working with `long double`s)
# - The Asylo tools versions of `libm.a` and `libc.a` do not include these symbols; they just have:
#   + `libm.a`:
#     * `fmax`, `logb` (for `double`)
#     * `fmaxf`, `logbf` (for `float`)
#   + `libc.a`
#     * `scalbn` (for `double`)
#     * `scalbnf` (for `float`)
# - Net cause: we're building the Rust library with a compiler that supports log double but linking
#   with libraries that don't.
genrule(
    name = "oak_runtime_stripped",
    srcs = [":oak_runtime"],
    outs = ["oak_runtime_stripped.a"],
    cmd = "cp $< $@ && chmod +rw $@ && ar d $@ divxc3.o",
)

# Wrapper rule to expose the resulting static library as a statically linked cc_library and
# corresponding header so that it can be depended on by other cc_library and cc_binary rules.
#
# TODO: There seems to be something wrong with this rule related to caching in Bazel.
# To reproduce:
# - change src/lib.rs and introduce a syntax error
# - bazel build //rust/oak_runtime:wrapper
# - this should produce a compile error, instead Bazel is still caching the old artifact
# The final link of //oak/server/asylo:oak uses oak_runtime_stripped.a not libwrapper.a. Similarly,
# a change to the Rust file does induce a rebuild when doing bazel build //oak/server/dev:oak. So is
# Bazel maybe doing something special for a target with a single src that is itself a .a file?
cc_library(
    name = "wrapper",
    srcs = [":oak_runtime_stripped"],
    hdrs = ["oak_runtime.h"],
    linkstatic = True,
    visibility = ["//oak/server:__subpackages__"],
)
