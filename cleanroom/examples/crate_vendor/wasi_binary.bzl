#
# Copyright 2026 The Project Oak Authors
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

"""Provides a rule to transition a target to the wasm32-wasip2 platform."""

def _wasi_transition_impl(settings, attr):
    _ignore = (settings, attr)
    return {
        "//command_line_option:platforms": ["//:wasm32-wasip2"],
    }

wasi_transition = transition(
    implementation = _wasi_transition_impl,
    inputs = [],
    outputs = ["//command_line_option:platforms"],
)

def _wasi_binary_impl(ctx):
    target = ctx.attr.binary[0]

    # We want to propagate the default outputs (the .wasm file usually)
    exec_file = target[DefaultInfo].files.to_list()[0]

    out = ctx.actions.declare_file(ctx.label.name + ".wasm")
    ctx.actions.run_shell(
        inputs = [exec_file],
        outputs = [out],
        command = "cp %s %s" % (exec_file.path, out.path),
    )

    return [DefaultInfo(
        files = depset([out]),
        executable = out,
    )]

wasi_binary = rule(
    implementation = _wasi_binary_impl,
    attrs = {
        "binary": attr.label(
            cfg = wasi_transition,
        ),
        "_allowlist_function_transition": attr.label(
            default = "@bazel_tools//tools/allowlists/function_transition_allowlist",
        ),
    },
    executable = True,
)
