def oak_copts():
    return [
        "-std=c++11",
        "-fno-rtti",
        "-fno-exceptions",
        "-fno-threadsafe-statics",
        "-fno-stack-protector",
        "-fno-use-cxa-atexit",
        "-fno-unwind-tables",
        "-ffunction-sections",
        "-fdata-sections",
        "-fmessage-length=0",
        "-Wall",
        "-Werror",
        "-Wdouble-promotion",
        "-Wshadow",
        "-Wunused-variable",
        "-Wunused-function",
        "-Wswitch",
        "-Wvla",
        "-Wextra",
        "-Wmissing-field-initializers",
        "-Wstrict-aliasing",
        "-Wno-sign-compare",
        "-Wno-unused-parameter",
        "-Wno-ignored-attributes",
        "-Wnon-virtual-dtor",
        "-DFARMHASH_NO_CXX_STRING",
        "-DTF_LITE_STATIC_MEMORY",
        "-Icc/tflite_micro/oak",
        "-Icc/tflite_micro/generated",
        "-Icc/tflite_micro/generated/third_party/flatbuffers/include",
        "-Icc/tflite_micro/generated/third_party/gemmlowp",
        "-Icc/tflite_micro/generated/third_party/ruy",
    ] + select({
        "//cc/tflite_micro/oak:no_sse": [],
        "//conditions:default": ["-msse4.2"],
    }) + select({
        "//cc/tflite_micro/oak:no_opt": ["-O0"],
        "//conditions:default": ["-O3"],
    })

def generate_cc_arrays(name, src, out, visibility = None):
    native.genrule(
        name = name,
        srcs = [
            src,
        ],
        outs = [
            out,
        ],
        cmd = "python3 $(location //cc/tflite_micro/tools:generate_cc_arrays) $@ $<",
        tools = ["//cc/tflite_micro/tools:generate_cc_arrays"],
        visibility = visibility,
    )
