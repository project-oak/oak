# Description:
#   TensorFlow Lite for Microcontrollers "gesture recognition" example.
load("//tensorflow/lite/micro:build_def.bzl", "generate_cc_arrays")

package(
    default_visibility = ["//visibility:public"],
    # Disabling layering_check because of http://b/177257332
    features = ["-layering_check"],
    licenses = ["notice"],
)

generate_cc_arrays(
    name = "generated_magic_wand_model_cc",
    src = "magic_wand.tflite",
    out = "magic_wand_model_data.cc",
)

generate_cc_arrays(
    name = "generated_magic_wand_model_hdr",
    src = "magic_wand.tflite",
    out = "magic_wand_model_data.h",
)

cc_library(
    name = "magic_wand_model_data",
    srcs = [
        ":generated_magic_wand_model_cc",
    ],
    hdrs = [
        ":generated_magic_wand_model_hdr",
    ],
)

cc_library(
    name = "sample_feature_data",
    srcs = [
        "ring_micro_features_data.cc",
        "slope_micro_features_data.cc",
    ],
    hdrs = [
        "ring_micro_features_data.h",
        "slope_micro_features_data.h",
    ],
)

cc_test(
    name = "magic_wand_test",
    srcs = [
        "magic_wand_test.cc",
    ],
    deps = [
        ":magic_wand_model_data",
        ":sample_feature_data",
        "//tensorflow/lite/micro:micro_framework",
        "//tensorflow/lite/micro:micro_log",
        "//tensorflow/lite/micro:op_resolvers",
        "//tensorflow/lite/micro/testing:micro_test",
        "//tensorflow/lite/schema:schema_fbs",
    ],
)

cc_library(
    name = "constants",
    hdrs = [
        "constants.h",
    ],
)

cc_library(
    name = "accelerometer_handler",
    srcs = [
        "accelerometer_handler.cc",
    ],
    hdrs = [
        "accelerometer_handler.h",
    ],
    deps = [
        "//tensorflow/lite/c:common",
    ],
)

cc_test(
    name = "accelerometer_handler_test",
    srcs = [
        "accelerometer_handler_test.cc",
    ],
    deps = [
        ":accelerometer_handler",
        "//tensorflow/lite/c:common",
        "//tensorflow/lite/micro:micro_framework",
        "//tensorflow/lite/micro:op_resolvers",
        "//tensorflow/lite/micro/testing:micro_test",
    ],
)

cc_library(
    name = "gesture_predictor",
    srcs = [
        "gesture_predictor.cc",
    ],
    hdrs = [
        "gesture_predictor.h",
    ],
    deps = [
        ":constants",
    ],
)

cc_test(
    name = "gesture_predictor_test",
    srcs = [
        "gesture_predictor_test.cc",
    ],
    deps = [
        ":constants",
        ":gesture_predictor",
        "//tensorflow/lite/micro:micro_framework",
        "//tensorflow/lite/micro/testing:micro_test",
    ],
)

cc_library(
    name = "output_handler",
    srcs = [
        "output_handler.cc",
    ],
    hdrs = [
        "output_handler.h",
    ],
    deps = [
        "//tensorflow/lite/c:common",
        "//tensorflow/lite/micro:micro_log",
    ],
)

cc_test(
    name = "output_handler_test",
    srcs = [
        "output_handler_test.cc",
    ],
    deps = [
        ":output_handler",
        "//tensorflow/lite/c:common",
        "//tensorflow/lite/micro:micro_framework",
        "//tensorflow/lite/micro/testing:micro_test",
    ],
)

cc_binary(
    name = "magic_wand",
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
        ":accelerometer_handler",
        ":constants",
        ":gesture_predictor",
        ":magic_wand_model_data",
        ":output_handler",
        "//tensorflow/lite/micro:micro_framework",
        "//tensorflow/lite/micro:op_resolvers",
        "//tensorflow/lite/micro:system_setup",
        "//tensorflow/lite/schema:schema_fbs",
    ],
)
