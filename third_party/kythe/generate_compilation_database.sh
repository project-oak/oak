#!/bin/bash

# Generates a compile_commands.json file at $(bazel info execution_root) for
# your Clang tooling needs.

BAZEL_ROOT="$(bazel info execution_root)"
pushd "$BAZEL_ROOT" > /dev/null
echo "[" > compile_commands.json
COUNT=0
find . -name '*.compile_command.json' -print0 | while read -r -d '' fname; do
  if ((COUNT++)); then
    echo ',' >> compile_commands.json
  fi
  sed -e "s|@BAZEL_ROOT@|$BAZEL_ROOT|g" < "$fname" | \
  # Clang doesn't recognize '-fno-canonical-system-headers'.
  sed -e "s|-fno-canonical-system-headers|-no-canonical-prefixes|g" >> compile_commands.json
done
echo "]" >> compile_commands.json
popd > /dev/null
