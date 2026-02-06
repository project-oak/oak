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

package(licenses = ["notice"])

# This rule captures _way_ too much.
#
# The only files excluded are ones that confuse bazel (eg they've got a '\' or ':' in the file name; for the former, systemd is the main culprit, for the latter, Perl).
#
# We should first figure out what files are _actually_ needed by the compilers, and after that remove everything we don't need from the sysroot.
filegroup(
    name = "sysroot",
    srcs = glob(
        ["**"],
        exclude = [
            "lib/systemd/**",
            "usr/lib/systemd/**",
            "usr/share/man/**",
            "var/lib/dpkg/**",
        ],
    ),
    visibility = ["//visibility:public"],
)

# Provides the dynamic linker library.
filegroup(
    name = "linker_library",
    srcs = [
        "usr/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2",
    ],
    visibility = ["//visibility:public"],
)

# Provides only the shared libraries needed by Oak Conatiners Stage 1.
filegroup(
    name = "stage1_shared_libraries",
    srcs = [
        "usr/lib/x86_64-linux-gnu/libc.so.6",
        "usr/lib/x86_64-linux-gnu/libgcc_s.so.1",
        "usr/lib/x86_64-linux-gnu/libm.so.6",
    ],
    visibility = ["//visibility:public"],
)
