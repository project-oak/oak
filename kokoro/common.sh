#!/usr/bin/env bash

set -o errexit
set -o nounset
set -o xtrace
set -o pipefail

export CI=kokoro
export RUST_BACKTRACE=1
export RUST_LOG=debug
export XDG_RUNTIME_DIR=/var/run
export JUST_TIMESTAMP=true
export JUST_TIMESTAMP_FORMAT='JUST:%H:%M:%S%.3f'

# Make sure we're in the root of the repository.
cd "$(dirname "$0")/.."
