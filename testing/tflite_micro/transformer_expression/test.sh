#!/bin/bash
SCRIPT_DIR="$(dirname "$(readlink -f "$0")")"
WORKSPACE_ROOT_DIR="${SCRIPT_DIR}/../../.."

pushd "${WORKSPACE_ROOT_DIR}" >/dev/null
trap "popd > /dev/null" EXIT

# Build
bazel build --copt=-g --strip=never //testing/tflite_micro/transformer_expression

# Run
bazel-bin/testing/tflite_micro/transformer_expression/transformer_expression
status=$?

# Check results
if (( $status >= 200 )); then
    echo -e "\nError executing tflite_init or tflite_run (${status})\n"
elif (( $status > 0 )); then
    echo -e "\nOutput not accurate at ${status}-th test set\n"
else
    echo -e "\nPASSED\n"
fi
