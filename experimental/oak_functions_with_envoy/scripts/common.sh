#!/usr/bin/env bash
# shellcheck disable=SC2034  # Unused variables OK as this script is `source`d.

readonly SCRIPTS_DIR="$(dirname "$0")/../../../scripts/"
# shellcheck source=scripts/common
source "$SCRIPTS_DIR/common"

readonly ENVOY_CLIENT_IMAGE_NAME='gcr.io/oak-ci/oak-functions-with-envoy-client'
readonly ENVOY_SERVER_IMAGE_NAME='gcr.io/oak-ci/oak-functions-with-envoy-server'
readonly ENVOY_SERVER_INSTANCE_NAME='oak-functions-with-envoy-example'
