#!/usr/bin/env bash
set -o errexit
set -o nounset
set -o pipefail

output=$("${PROGRAM}")

expect="Server starting
Client is writing: Hello Server
Server responded: revreS olleH
Server completed."

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
