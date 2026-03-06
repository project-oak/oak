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

    ctx.actions.expand_template(
        template = ctx.file.template,
        output = out,
        substitutions = {
            "{{ARGS}}": args_json,
            "{{ENV}}": env_json,
            "{{ROOT_PATH}}": ctx.attr.root_path,
        },
    )
    return [DefaultInfo(files = depset([out]))]

oak_app_config = rule(
    implementation = _oak_app_config_impl,
    attrs = {
        "template": attr.label(
            default = "//oak_containers/app_base:config.json.tpl",
            allow_single_file = True,
        ),
        "args": attr.string_list(doc = "Arguments to pass to the entrypoint."),
        "env": attr.string_dict(doc = "Environment variables to set (dictionary)."),
        "root_path": attr.string(
            default = "rootfs",
            doc = "The directory containing the root filesystem inside the bundle.",
        ),
    },
    doc = "Generates a based Oak Containers-compatible config.json file.",
)

def app_bundle(
        name,
        binary,
        base_image = "@oak_containers_app_base//:flat",
        args = None,
        env = None,
        entrypoint_path = "/usr/local/bin/",
        root_path = "rootfs",
        **kwargs):
    """Generates an OCI-like bundle tarball for an application.

    The tarball contains:
    - config.json at the root.
    - Contents of @app_base and the binary, all prefixed with /{root_path}.
    - The binary is at {entrypoint_path}{binary_name}.

    Args:
        name: The name of the target.
        binary: The label of the binary target to include.
        base_image: The label of the base image target to use. If not provided,
            it will default to @oak_containers/app_base:flat, a Debian 12 image with
            only the base-files package installed.
        args: Optional list of arguments to pass to the application. The first argument
            will always be the path to the binary.
        env: Optional dictionary of environment variables. Standard variables like
            PATH and HOME have defaults but can be overridden.
        entrypoint_path: The directory in the rootfs where the binary will be placed.
            Defaults to /usr/local/bin/.
        root_path: The directory name in the bundle containing the filesystem.
            Defaults to "rootfs".
        **kwargs: Additional arguments to pass to the final flatten rule.
    """
    binary_label = native.package_relative_label(binary)
    binary_name = paths.basename(binary_label.name)

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
        env = env if env != None else {},
        root_path = root_path,
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
