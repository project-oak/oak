# Copyright 2025 The Project Oak Authors
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

"""Bazel build definitions for micro RPC."""

load("@com_google_protobuf//bazel/common:proto_info.bzl", "ProtoInfo")
load("@rules_rust//rust:defs.bzl", "rust_library")

def _generate_service_lib_impl(ctx):
    if len(ctx.attr.srcs) != 1:
        fail("The 'srcs' attribute must contain exactly one proto_library target.")

    main_target = ctx.attr.srcs[0]
    proto_info = main_target[ProtoInfo]

    output_file = ctx.actions.declare_file(ctx.attr.out_filename)
    outputs_dir = ctx.actions.declare_directory(ctx.attr.name + ".out_dir")

    args = ctx.actions.args()
    args.add_joined("--files-to-compile", proto_info.check_deps_sources, join_with = ",")
    args.add_joined("--proto-source-roots", proto_info.transitive_proto_path, join_with = ",")
    args.add("--out-filename", output_file)
    args.add("--out-dir", outputs_dir.path)
    args.add("--protoc", ctx.file._protoc.path)
    args.add("--extern-paths", json.encode(ctx.attr.extern_paths))

    ctx.actions.run(
        executable = ctx.executable._generator,
        inputs = proto_info.transitive_sources,
        outputs = [outputs_dir, output_file],
        arguments = [args],
        tools = [ctx.file._protoc],
    )

    return [DefaultInfo(files = depset([outputs_dir, output_file]))]

_generate_service_lib = rule(
    implementation = _generate_service_lib_impl,
    attrs = {
        "srcs": attr.label_list(providers = [ProtoInfo], mandatory = True, allow_files = False),
        "out_filename": attr.string(mandatory = True),
        "extern_paths": attr.string_dict(mandatory = True),
        "_generator": attr.label(
            default = Label("//micro_rpc_build:generator"),
            executable = True,
            cfg = "exec",
        ),
        "_protoc": attr.label(
            default = Label("@com_google_protobuf//:protoc"),
            allow_single_file = True,
            cfg = "exec",
        ),
    },
)

def rust_micro_rpc_service(
        name,
        srcs = [],
        deps = [],
        extern_paths = {},
        **kwargs):
    """A macro that generates a Rust micro RPC service library.

    Args:
        name: The name of the micro RPC service library.
        srcs: Proto files to generate Rust micro RPC service code from.
        deps: Dependencies on external Rust libraries required by the generated service library.
        extern_paths: A mapping of (fully-qualified) proto package names to external crate paths.
            Also see https://docs.rs/prost-build/latest/prost_build/struct.Config.html#method.extern_path.
        **kwargs: Any other arguments to rust_library.
    """

    generate_service_lib_name = name + "_gen"
    _generate_service_lib(
        name = generate_service_lib_name,
        srcs = srcs,
        out_filename = name + ".rs",
        extern_paths = extern_paths,
    )

    rust_library(
        name = name,
        srcs = [":" + generate_service_lib_name],
        proc_macro_deps = [
            Label("@oak_crates_index//:prost-derive"),
        ],
        deps = [
            Label("//micro_rpc"),
            Label("@oak_crates_index//:prost"),
            Label("@oak_crates_index//:prost-types"),
        ] + deps,
        **kwargs
    )
