load(
    "@com_github_tensorflow_tflite_micro//tensorflow/lite/micro:build_def.bzl",
    "generate_cc_arrays",
    "micro_copts",
)

package(
    default_visibility = ["//visibility:public"],
    features = ["-layering_check"],
    licenses = ["notice"],
)

generate_cc_arrays(
    name = "generated_hello_world_model_cc",
    src = "hello_world.tflite",
    out = "hello_world_model_data.cc",
)

generate_cc_arrays(
    name = "generated_hello_world_model_hdr",
    src = "hello_world.tflite",
    out = "hello_world_model_data.h",
)

cc_library(
    name = "model",
    srcs = [
        ":generated_hello_world_model_cc",
    ],
    hdrs = [
        ":generated_hello_world_model_hdr",
    ],
    copts = micro_copts(),
)

cc_library(
    name = "output_handler",
    srcs = [
        "output_handler.cc",
    ],
    hdrs = [
        "output_handler.h",
    ],
    copts = micro_copts(),
    deps = [
        "@com_github_tensorflow_tflite_micro//tensorflow/lite/c:common",
        "@com_github_tensorflow_tflite_micro//tensorflow/lite/micro:micro_log",
    ],
)

cc_library(
    name = "constants",
    srcs = [
        "constants.cc",
    ],
    hdrs = [
        "constants.h",
    ],
    copts = micro_copts(),
)

cc_binary(
    name = "hello_world",
    srcs = [
        "main.cc",
        "main_functions.cc",
        "main_functions.h",
    ],
    copts = [
        "-Werror",
        "-Wsign-compare",
    ],
    deps = [
        ":constants",
        ":model",
        ":output_handler",
        "@com_github_tensorflow_tflite_micro//tensorflow/lite/micro:micro_framework",
        "@com_github_tensorflow_tflite_micro//tensorflow/lite/micro:micro_log",
        "@com_github_tensorflow_tflite_micro//tensorflow/lite/micro:op_resolvers",
        "@com_github_tensorflow_tflite_micro//tensorflow/lite/micro:system_setup",
        "@com_github_tensorflow_tflite_micro//tensorflow/lite/schema:schema_fbs",
    ],
)
