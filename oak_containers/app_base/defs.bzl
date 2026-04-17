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

"""Macros for generating the app_base config.json with a custom entrypoint."""

load("@bazel_skylib//lib:paths.bzl", "paths")
load("@rules_distroless//distroless:defs.bzl", "flatten")
load("@rules_pkg//pkg:mappings.bzl", "pkg_files")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")

DEFAULT_ENV = {
    "PATH": "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
    "TERM": "xterm",
    "SSL_CERT_FILE": "/etc/ssl/certs/ca-certificates.crt",
    "HOME": "/root",
}

# Default rlimits matching the OCI runtime spec defaults.
DEFAULT_PROCESS_RLIMITS_JSON = '[{"type":"RLIMIT_NOFILE","hard":1024,"soft":1024}]'

def _oak_app_config_impl(ctx):
    out = ctx.actions.declare_file(ctx.label.name + ".json")

    # Start with defaults and overlay user-provided environment variables
    env_dict = dict(DEFAULT_ENV)
    env_dict.update(ctx.attr.env)

    # OCI config.json expects env as a list of "KEY=VALUE" strings
    env_list = ["{}={}".format(k, v) for k, v in sorted(env_dict.items())]

    # Process args and env into JSON array strings
    args_json = json.encode(ctx.attr.args)
    env_json = json.encode(env_list)

    extra_mounts_str = ""
    if ctx.attr.extra_mounts:
        # Prepend a comma because we're injecting into the end of an array
        extra_mounts_str = ",\n        " + ",\n        ".join(ctx.attr.extra_mounts)

    # Build the rlimits JSON array from the process_rlimits attribute.
    # Each entry is a JSON object string. If not specified, use the defaults.
    if ctx.attr.process_rlimits:
        rlimits_json = "[" + ",".join(ctx.attr.process_rlimits) + "]"
    else:
        rlimits_json = DEFAULT_PROCESS_RLIMITS_JSON

    ctx.actions.expand_template(
        template = ctx.file._template,
        output = out,
        substitutions = {
            "{{ARGS}}": args_json,
            "{{ENV}}": env_json,
            "{{ROOT_PATH}}": ctx.attr.root_path,
            "{{EXTRA_MOUNTS}}": extra_mounts_str,
            "{{PROCESS_RLIMITS}}": rlimits_json,
        },
    )
    return [DefaultInfo(files = depset([out]))]

oak_app_config = rule(
    implementation = _oak_app_config_impl,
    attrs = {
        "_template": attr.label(
            default = "//oak_containers/app_base:config.json.tpl",
            allow_single_file = True,
        ),
        "args": attr.string_list(doc = "Arguments to pass to the entrypoint."),
        "env": attr.string_dict(doc = "Environment variables to set (dictionary)."),
        "root_path": attr.string(
            default = "rootfs",
            doc = "The directory containing the root filesystem inside the bundle.",
        ),
        "extra_mounts": attr.string_list(doc = "List of extra JSON mount strings to include in config.json."),
        "process_rlimits": attr.string_list(
            doc = "List of rlimit JSON object strings. Each entry should be a JSON object with 'type', 'hard', and 'soft' keys. If empty, defaults to RLIMIT_NOFILE 1024/1024.",
        ),
    },
    doc = "Generates a based Oak Containers-compatible config.json file.",
)

def _app_bundle_impl(
        name,
        binary,
        base_image,
        args,
        env,
        entrypoint_path,
        root_path,
        extra_mounts,
        process_rlimits,
        **kwargs):
    binary_name = paths.basename(binary.name)

    # Ensure entrypoint_path ends with a slash
    if not entrypoint_path.endswith("/"):
        entrypoint_path += "/"

    full_entrypoint = entrypoint_path + binary_name

    # The first argument is always the binary itself
    actual_args = [full_entrypoint]
    if args:
        actual_args.extend(args)

    config_target = name + "_config_json"
    oak_app_config(
        name = config_target,
        args = actual_args,
        env = env,
        root_path = root_path,
        extra_mounts = extra_mounts,
        process_rlimits = process_rlimits,
    )

    pkg_files(
        name = name + "_config_file",
        srcs = [":" + config_target],
        renames = {
            ":" + config_target: "config.json",
        },
    )

    pkg_tar(
        name = name + "_config_tar",
        srcs = [":" + name + "_config_file"],
    )

    pkg_tar(
        name = name + "_binary_tar",
        srcs = [binary],
        package_dir = "/" + root_path + entrypoint_path,
    )

    pkg_tar(
        name = name + "_app_base_tar",
        deps = [base_image],
        package_dir = "./" + root_path,
    )

    flatten(
        name = name,
        tars = [
            ":" + name + "_config_tar",
            ":" + name + "_binary_tar",
            ":" + name + "_app_base_tar",
        ],
        **kwargs
    )

app_bundle = macro(
    doc = """Generates an OCI-like bundle tarball for an application.

The tarball contains:
- config.json at the root.
- Contents of @app_base and the binary, all prefixed with /{root_path}.
- The binary is at {entrypoint_path}{binary_name}.
""",
    implementation = _app_bundle_impl,
    inherit_attrs = flatten,
    attrs = {
        "binary": attr.label(
            doc = "The label of the binary target to include.",
            configurable = False,
            mandatory = True,
        ),
        "base_image": attr.label(
            doc = "The label of the base image target to use. If not provided, it will default to a Debian 12 image with only the base-files package installed.",
            default = "@oak_containers_app_base//:flat",
            configurable = False,
        ),
        "args": attr.string_list(
            doc = "List of arguments to pass to the application. The first argument will always be the path to the binary.",
            configurable = False,
        ),
        "env": attr.string_dict(
            doc = "Dictionary of environment variables. Standard variables like PATH and HOME have defaults but can be overridden.",
            configurable = False,
        ),
        "entrypoint_path": attr.string(
            doc = "The directory in the rootfs where the binary will be placed.",
            default = "/usr/local/bin",
            configurable = False,
        ),
        "root_path": attr.string(
            doc = "The directory name in the bundle containing the filesystem.",
            default = "rootfs",
            configurable = False,
        ),
        "extra_mounts": attr.string_list(
            doc = "List of extra mounts as JSON strings to add to the container config.json.",
            configurable = False,
        ),
        "process_rlimits": attr.string_list(
            doc = "List of rlimit JSON object strings with 'type', 'hard', and 'soft' keys. Overrides the default RLIMIT_NOFILE 1024/1024.",
            configurable = False,
        ),
        "tars": None,
    },
)
