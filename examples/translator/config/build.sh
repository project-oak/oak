#!/usr/bin/env bash

readonly DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
readonly MODULES_DIR="${DIR}/../../target/wasm32-unknown-unknown/release"

bazel run //oak/common:app_config_serializer -- \
    --textproto="${DIR}/config.textproto"\
    --modules="app:${MODULES_DIR}/translator.wasm"\
    --output_file="${DIR}/config.bin"
