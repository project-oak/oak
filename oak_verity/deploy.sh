#!/bin/bash
# This script builds the container image, constructs the image digest,
# and then deploys or updates the GCE instance using Terraform.

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
readonly TF_DIR="oak_verity"

# --- Script ---

echo "Building container image and calculating digest..."
# We run the :image.digest target which just builds the image locally
# and creates the digest file. This is the same digest that will be created when pushing the image to the remote registry.
bazel build //oak_verity/gcp:image.digest

# First push the image. The command returns the full URL with the digest of the image that was just pushed.
FULL_IMAGE_DIGEST="$(bazel run //oak_verity/gcp:image_push)"

echo "Image digest: ${FULL_IMAGE_DIGEST}"

# Always initialize Terraform.
echo "Initializing Terraform..."
terraform -chdir="${TF_DIR}" init

echo "Running Terraform to deploy the instance..."
# We pass the variables directly on the command line.
# Terraform will prompt you to confirm the changes.
terraform -chdir="${TF_DIR}" apply -auto-approve \
  -var="gcp_project_id=${GCP_PROJECT_ID}" \
  -var="image_digest=${FULL_IMAGE_DIGEST}" \
  -var="zone=${ZONE}"

INSTANCE_ID=$(terraform -chdir="${TF_DIR}" output -raw instance_id)
echo "Instance ID: ${INSTANCE_ID}"
