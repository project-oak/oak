#!/usr/bin/env bash

readonly DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
readonly EXAMPLES_OUTPUT_DIR="${DIR}/../../../bazel-emscripten-bin/examples"
readonly OUT_DIR="${DIR}/../bin"
mkdir --parents "${OUT_DIR}"

bazel run //oak/common:app_config_serializer -- \
    --textproto="${DIR}/config.textproto"\
    --modules="app:${EXAMPLES_OUTPUT_DIR}/tensorflow/module/cpp/tensorflow_micro.wasm"\
    --output_file="${OUT_DIR}/config_cpp.bin"