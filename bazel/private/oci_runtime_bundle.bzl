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
"""Implementation details for the oci_runtime_bundle macro."""

def _oci_runtime_bundle_impl(ctx):
    image = ctx.file.image
    bundle = ctx.outputs.bundle
    umoci = ctx.toolchains["@umoci//:toolchain_type"].umociinfo.bin
    yq = ctx.toolchains["@aspect_bazel_lib//lib:yq_toolchain_type"].yqinfo.bin
    config_patch = ctx.attr.config_patch.replace('"', '\\"')

    # Since bazel doesn't support actions that create directory artifacts
    # containing symlinks, we use a shell script so that a single action can
    # unpack the container image and then re-pack it into a tar file.
    executable = ctx.actions.declare_file("{}.tar.sh".format(ctx.label.name))

    ctx.actions.expand_template(
        template = ctx.file._tpl,
        output = executable,
        is_executable = True,
        substitutions = {
            "{{umoci}}": umoci.path,
            "{{yq}}": yq.path,
            "{{config_patch}}": config_patch,
        },
    )

    ctx.actions.run(
        executable = executable,
        inputs = [image],
        outputs = [bundle],
        tools = [umoci, yq],
        arguments = [image.path, bundle.path],
        mnemonic = "OciRuntimeBundle",
        progress_message = "Converting %{input} to an OCI runtime bundle",
    )

_oci_runtime_bundle = rule(
    implementation = _oci_runtime_bundle_impl,
    attrs = {
        "image": attr.label(allow_single_file = True),
        "bundle": attr.output(),
        "config_patch": attr.string(
            default = "",
            doc = "Patch for yq to apply to the OCI runtime bundle config.json",
        ),
        "_tpl": attr.label(
            allow_single_file = True,
            default = ":oci_runtime_bundle.sh.tpl",
        ),
    },
    toolchains = [
        "@umoci//:toolchain_type",
        "@aspect_bazel_lib//lib:yq_toolchain_type",
        "@bazel_tools//tools/sh:toolchain_type",
    ],
)

def oci_runtime_bundle(name, image, **kwargs):
    """Converts an oci_image to a OCI runtime bundle tar.

    Args:
        name: the target name to produce. Building this target will generate a
          "{name}.tar" output file.
        image: the oci_image target to convert.
        **kwargs: additional arguments passed to the rule (e.g., visibility).
    """
    _oci_runtime_bundle(
        name = name,
        bundle = "{}.tar".format(name),
        image = image,
        **kwargs
    )
