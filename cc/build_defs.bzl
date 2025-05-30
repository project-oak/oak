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

"""Provides a rule that outputs a monolithic static library."""

load(
    "@bazel_tools//tools/cpp:toolchain_utils.bzl",
    "find_cpp_toolchain",
    "use_cpp_toolchain",
)
load("@rules_cc//cc/common:cc_info.bzl", "CcInfo")

# Bazel rule for collecting the object files that a target depends on.
# Modified from https://github.com/bazelbuild/bazel/issues/1920
def _cc_static_library_impl(ctx):
    output_lib = ctx.actions.declare_file("lib{}.a".format(ctx.attr.name))
    output_flags = ctx.actions.declare_file("lib{}.link".format(ctx.attr.name))

    cc_toolchain = find_cpp_toolchain(ctx)

    # Aggregate linker inputs of all dependencies
    lib_sets = []
    for dep in ctx.attr.deps:
        lib_sets.append(dep[CcInfo].linking_context.linker_inputs)
    input_depset = depset(transitive = lib_sets)

    # Collect user link flags and make sure they are unique
    unique_flags = {}
    for inp in input_depset.to_list():
        unique_flags.update({
            flag: None
            for flag in inp.user_link_flags
        })
    link_flags = unique_flags.keys()

    # Collect static libraries
    libs = []
    for inp in input_depset.to_list():
        for lib in inp.libraries:
            if lib.pic_static_library:
                libs.append(lib.pic_static_library)
            elif lib.static_library:
                libs.append(lib.static_library)

    script_file = ctx.actions.declare_file("lib{}.mri".format(ctx.attr.name))
    commands = ["create {}".format(output_lib.path)]
    for lib in libs:
        commands.append("addlib {}".format(lib.path))
    commands.append("save")
    commands.append("end")
    ctx.actions.write(
        output = script_file,
        content = "\n".join(commands) + "\n",
    )

    ctx.actions.run_shell(
        command = "{} -M < {}".format(cc_toolchain.ar_executable, script_file.path),
        inputs = [script_file] + libs + cc_toolchain.all_files.to_list(),
        outputs = [output_lib],
        mnemonic = "ArMerge",
        progress_message = "Merging static library {}".format(output_lib.path),
    )
    ctx.actions.write(
        output = output_flags,
        content = "\n".join(link_flags) + "\n",
    )
    return [
        DefaultInfo(files = depset([output_flags, output_lib])),
    ]

cc_static_library = rule(
    implementation = _cc_static_library_impl,
    attrs = {
        "deps": attr.label_list(),
        "_cc_toolchain": attr.label(
            default = "@bazel_tools//tools/cpp:current_cc_toolchain",
        ),
    },
    toolchains = use_cpp_toolchain(),
)
