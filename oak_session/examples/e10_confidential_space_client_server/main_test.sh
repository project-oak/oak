#!/bin/bash
set -o errexit
set -o nounset
set -o pipefail

output=$("${PROGRAM}")

expect="Open!
Client is writing: Hello Server
The server read back: Hello Server"

if [ "${output}" == "${expect}" ]; then
  echo "Yay"
  exit 0
else
  echo "Expected:"
  echo "${expect}"
  echo ""
  echo "Received:"
  echo "${output}"
  exit 1
fi
