#!/usr/bin/env bash

readonly EXPERIMENTAL_SCRIPTS_DIR="$(dirname "$0")"
# shellcheck source=experimental/envoy_proxy/scripts/common.sh
source "$EXPERIMENTAL_SCRIPTS_DIR/common.sh"

# shellcheck source=scripts/gcp_common
source "$SCRIPTS_DIR/gcp_common"

# Authenticate as the service account
gcloud auth activate-service-account \
  --project="${GCP_PROJECT_ID}" \
  --key-file="${GCP_ACCOUNT_FILE}"

# Delete the application from Cloud Run.
gcloud beta run services delete "${ENVOY_SERVER_INSTANCE_NAME}" \
  --region=europe-west2 \
  --platform=managed
