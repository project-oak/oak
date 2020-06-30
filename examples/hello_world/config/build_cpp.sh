#!/usr/bin/env bash

readonly DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
readonly EXAMPLES_OUTPUT_DIR="${DIR}/../../../bazel-wasm-bin/examples"

bazel run //oak/common:app_config_serializer -- \
    --textproto="${DIR}/config.textproto"\
    --modules="app:${EXAMPLES_OUTPUT_DIR}/hello_world/module/cpp/hello_world.wasm"\
    --output_file="${DIR}/config_cpp.bin"