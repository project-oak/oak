package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

cc_library(
    name = "wabt",
    srcs = glob(
        [
            "src/*.cc",
            "src/*.c",
            "src/interp/*.cc",
        ],
        exclude = [
            "src/test-*",
        ],
    ),
    hdrs = glob([
        "config.h",
        "src/*.h",
        "src/interp/*.h",
        "src/prebuilt/*.h",
    ]),
    textual_hdrs = [
        "src/opcode.def",
        "src/feature.def",
        "src/token.def",
        "src/prebuilt/wasm2c.include.h",
        "src/prebuilt/wasm2c.include.c",
        "src/prebuilt/lexer-keywords.cc",
    ],
    visibility = ["//visibility:public"],
)

cc_binary(
    name = "wat2wasm",
    srcs = ["src/tools/wat2wasm.cc"],
    deps = [":wabt"],
)

cc_binary(
    name = "wasm2wat",
    srcs = ["src/tools/wasm2wat.cc"],
    deps = [":wabt"],
)
