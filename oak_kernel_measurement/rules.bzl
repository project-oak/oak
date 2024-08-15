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
"""Bazel rule for generating kernel measurements."""

def _kernel_measurement_impl(ctx):
    setup_data = ctx.actions.declare_file(ctx.label.name + "_setup_data")
    image = ctx.actions.declare_file(ctx.label.name + "_image")
    ctx.actions.run(
        inputs = [ctx.file.src],
        outputs = [setup_data, image],
        executable = ctx.executable.measurement_tool,
        arguments = [
            "--kernel=" + ctx.file.src.path,
            "--kernel-setup-data-output=" + setup_data.path,
            "--kernel-image-output=" + image.path,
        ],
    )
    return [DefaultInfo(files = depset([setup_data, image]))]

kernel_measurement = rule(
    implementation = _kernel_measurement_impl,
    attrs = {
        "src": attr.label(mandatory = True, allow_single_file = True),
        "measurement_tool": attr.label(
            executable = True,
            cfg = "exec",
            allow_files = True,
            default = Label("//oak_kernel_measurement"),
        ),
    },
)
