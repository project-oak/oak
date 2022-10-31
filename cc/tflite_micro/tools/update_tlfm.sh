#!/bin/bash
set -o errexit

if [[ $# -ne 1 ]]; then
    echo "update_tflm.sh TFLM_SOURCE_DIR" >&2
    exit 2
fi

pushd "$(dirname "$0")" >/dev/null
trap "popd > /dev/null" EXIT

SCRIPT_DIR="$(dirname "$0")"
WORKSPACE_ROOT_DIR="${SCRIPT_DIR}/../../.."
TFLM_SOURCE_DIR="$@"
TFLM_GENERATED_DIR="/tmp/tflm_generated"

# Prune previously generated source tree if any.
rm -rf ${TFLM_GENERATED_DIR} 2>&1 >/dev/null

# Generate clean set of tflm source tree.
python3 ${TFLM_SOURCE_DIR}/tensorflow/lite/micro/tools/project_generation/create_tflm_tree.py ${TFLM_GENERATED_DIR}

# Prune old tflm sources cleanly.
rm -rf ${WORKSPACE_ROOT_DIR}/third_party/tflite-micro/tensorflow
rm -rf ${WORKSPACE_ROOT_DIR}/third_party/tflite-micro/LICENSE
rm -rf ${WORKSPACE_ROOT_DIR}/third_party/flatbuffers/include
rm -rf ${WORKSPACE_ROOT_DIR}/third_party/flatbuffers/LICENSE.txt
rm -rf ${WORKSPACE_ROOT_DIR}/third_party/gemmlowp/fixedpoint
rm -rf ${WORKSPACE_ROOT_DIR}/third_party/gemmlowp/internal
rm -rf ${WORKSPACE_ROOT_DIR}/third_party/gemmlowp/LICENSE
rm -rf ${WORKSPACE_ROOT_DIR}/third_party/ruy/ruy

# Copy over generated sources to corresponding directories.
cp -rf ${TFLM_GENERATED_DIR}/tensorflow ${WORKSPACE_ROOT_DIR}/third_party/tflite-micro/
cp -rf ${TFLM_GENERATED_DIR}/LICENSE ${WORKSPACE_ROOT_DIR}/third_party/tflite-micro/
cp -rf ${TFLM_GENERATED_DIR}/third_party/flatbuffers ${WORKSPACE_ROOT_DIR}/third_party/
cp -rf ${TFLM_GENERATED_DIR}/third_party/ruy ${WORKSPACE_ROOT_DIR}/third_party/
cp -rf ${TFLM_GENERATED_DIR}/third_party/gemmlowp ${WORKSPACE_ROOT_DIR}/third_party/
