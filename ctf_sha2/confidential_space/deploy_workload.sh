#!/bin/bash
# This script builds the container image, constructs the image digest,
# and then deploys or updates the GCE instance using Terraform.

# TODO: b/437925650 - Wrap this script in a sh_binary bazel target.

set -o errexit
set -o pipefail
set -o nounset
set -o xtrace
shopt -s inherit_errexit

# --- Configuration ---
# The GCP Project ID where the instance will be deployed.
# You can set this here or pass it as the first argument to the script.
GCP_PROJECT_ID="${1:-oak-examples-477357}"

# The GCP zone where the instance will be deployed.
# You can set this here or pass it as the second argument to the script.
ZONE="${2:-us-west1-b}"

# The directory containing the Terraform configuration.
readonly TF_DIR="ctf_sha2/confidential_space/terraform"

# --- Script ---

echo "Building container image and calculating digest..."
# We run the :image.digest target which just builds the image locally
# and creates the digest file. This is the same digest that will be created when pushing the image to the remote registry.
bazel build //ctf_sha2/confidential_space:workload_image.digest

# First push the image. The command returns the full URL with the digest of the image that was just pushed.
FULL_IMAGE_DIGEST="$(bazel run //ctf_sha2/confidential_space:workload_image_push)"

echo "Image digest: ${FULL_IMAGE_DIGEST}"

# Always initialize Terraform.
echo "Initializing Terraform..."
terraform -chdir="${TF_DIR}" init

echo "Running Terraform to deploy the instance..."
# We pass the variables directly on the command line.
# Terraform will prompt you to confirm the changes.
terraform -chdir="${TF_DIR}" apply \
  -var="gcp_project_id=${GCP_PROJECT_ID}" \
  -var="image_digest=${FULL_IMAGE_DIGEST}" \
  -var="zone=${ZONE}"

INSTANCE_ID=$(terraform -chdir="${TF_DIR}" output -raw instance_id)
echo "Instance ID: ${INSTANCE_ID}"

# Fetch logs containing the attestation token. Repeat until the relevant log entry appears.
while true; do
  # Find the attestation token log entry.
  LOG_ENTRIES=$(gcloud logging read "resource.type=\"gce_instance\" AND resource.labels.instance_id=\"${INSTANCE_ID}\" AND jsonPayload.MESSAGE:\"attestation_token\"" --project="${GCP_PROJECT_ID}" --format=json)
  LOG_ENTRIES_LENGTH=$(echo "${LOG_ENTRIES}" | jq 'length')
  if [[ ${LOG_ENTRIES_LENGTH} -gt 0 ]]; then
    # The token is in a JSON object which is itself string-encoded inside the JSON log entry.
    ATTESTATION_TOKEN=$(echo "${LOG_ENTRIES}" | jq -r '.[0].jsonPayload.MESSAGE' | jq -r '.attestation_token')
    break
  else
    echo "⏳ Waiting for more logs..."
    sleep 5
  fi
done

terraform -chdir="${TF_DIR}" destroy \
  -var="gcp_project_id=${GCP_PROJECT_ID}" \
  -var="image_digest=${FULL_IMAGE_DIGEST}" \
  -var="zone=${ZONE}"

echo "Attestation token: ${ATTESTATION_TOKEN}"
echo "View (decoded) at: https://jwt.io/#token=${ATTESTATION_TOKEN}"
