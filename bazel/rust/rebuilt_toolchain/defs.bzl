""" Helpers to rebuild the rust std libraries for a new toolchain. """

load("@bazel_skylib//lib:paths.bzl", "paths")

def _stdlib_bulid_transition_impl(_, __):
    return {
        "//command_line_option:extra_toolchains": [],
        "//command_line_option:compilation_mode": "opt",
        "//command_line_option:platforms": "//:x86_64-unknown-none-noavx",
    }

_stdlib_build_transition = transition(
    inputs = [],
    outputs = [
        "//command_line_option:extra_toolchains",
        "//command_line_option:compilation_mode",
        "//command_line_option:platforms",
    ],
    implementation = _stdlib_bulid_transition_impl,
)

def _with_stdlib_build_transition_impl(ctx):
    return [DefaultInfo(files = depset(ctx.files.srcs))]

with_stdlib_build = rule(
    doc = "Transitions to a different toolchain to rebuild the std libraries for the current toolchain.",
    implementation = _with_stdlib_build_transition_impl,
    attrs = {
        "srcs": attr.label_list(
            allow_files = True,
        ),
        "_allowlist_function_transition": attr.label(
            default = Label("@bazel_tools//tools/allowlists/function_transition_allowlist"),
        ),
    },
    cfg = _stdlib_build_transition,
)

def _toolchain_sysroot_impl(ctx):
    sysroot = ctx.attr.dirname
    outputs = []

    rustlibdir = paths.join(sysroot, "lib", "rustlib", ctx.attr.target_triple, "lib")
    rustbindir = paths.join(sysroot, "bin")

    for inp in ctx.files.srcs:
        if inp.short_path in ctx.attr.tools:
            out = ctx.actions.declare_file(paths.join(rustbindir, ctx.attr.tools[inp.short_path]))
        else:
            out = ctx.actions.declare_file(paths.join(rustlibdir, inp.basename))

        outputs.append(out)
        ctx.actions.symlink(output = out, target_file = inp)

    return [DefaultInfo(
        files = depset(outputs),
        runfiles = ctx.runfiles(files = outputs),
    )]

toolchain_sysroot = rule(
    implementation = _toolchain_sysroot_impl,
    attrs = {
        "dirname": attr.string(
            doc = "The directory where the sysroot will be created.",
            mandatory = True,
        ),
        "target_triple": attr.string(
            doc = "The target triple for the rlibs.",
            default = "x86_64-unknown-none",
        ),
        "srcs": attr.label_list(
            allow_files = True,
        ),
        "tools": attr.string_dict(
            doc = "A map from tool's short_path to its final name under bin/",
        ),
    },
)
