#!/usr/bin/env bash

readonly EXPERIMENTAL_SCRIPTS_DIR="$(dirname "$0")"
# shellcheck source=experimental/envoy_proxy/scripts/common.sh
source "$EXPERIMENTAL_SCRIPTS_DIR/common.sh"

# shellcheck source=scripts/gcp_common
source "$SCRIPTS_DIR/gcp_common"

docker push "${ENVOY_SERVER_IMAGE_NAME}:latest"

# Authenticate as the service account
gcloud auth activate-service-account \
  --project="${GCP_PROJECT_ID}" \
  --key-file="${GCP_ACCOUNT_FILE}"

# Deploy the application on Cloud Run.
gcloud beta run deploy "${ENVOY_SERVER_INSTANCE_NAME}" \
  --region=europe-west2 \
  --image="${ENVOY_SERVER_IMAGE_NAME}:latest" \
  --allow-unauthenticated \
  --concurrency=20 \
  --min-instances=1 \
  --max-instances=10 \
  --use-http2 \
  --platform=managed
