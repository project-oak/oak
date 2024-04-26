#!/usr/bin/env bash

# shellcheck source=./kokoro/common.sh
source "$(dirname "$0")/common.sh"

./scripts/docker_pull
# TODO: b/337266665 - Remove bazel-cache-test logic once we are satisfied with remote cache hits.
./scripts/docker_run nix develop .#ci --command just bazel-ci bazel-cache-test

# Upload the bazel execution logs as Kokoro artifacts so we can debug remote cache. This should
# be removed once the debugging is completed. We use the binaries folder only because it is
# already configured to receive and upload artifacts to CNS.
mkdir --parents "${KOKORO_ARTIFACTS_DIR}/binaries/test"
cp --preserve=timestamps \
    ./target/bazel_* \
    "${KOKORO_ARTIFACTS_DIR}/binaries/test"
