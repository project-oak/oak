"""Rules to build native modules for Oak Functions on Oak Containers."""

def oak_functions_native_module(name, deps, **kwargs):
    native.cc_binary(
        name = name,
        linkshared = 1,
        linkstatic = 1,
        linkopts = [
            "-Wl,--version-script,$(location //cc/oak_functions/native_sdk:symbols.map.ld)",
        ],
        deps = [
            "//cc/oak_functions/native_sdk",
            "symbols.map.ld",
        ] + deps,
        **kwargs
    )
