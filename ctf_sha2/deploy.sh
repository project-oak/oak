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

# The directory containing the Terraform configuration.
readonly TF_DIR="ctf_sha2"

# --- Script ---

echo "Building container image and calculating digest..."
# We run the :image.digest target which just builds the image locally
# and creates the digest file. This is the same digest that will be created when pushing the image to the remote registry.
bazel build //ctf_sha2:image.digest

# First push the image. The command returns the full URL with the digest of the image that was just pushed.
FULL_IMAGE_DIGEST="$(bazel run //ctf_sha2:image_push)"

echo "Image digest: ${FULL_IMAGE_DIGEST}"

# Always initialize Terraform.
echo "Initializing Terraform..."
terraform -chdir="${TF_DIR}" init

echo "Running Terraform to deploy the instance..."
# We pass the variables directly on the command line.
# Terraform will prompt you to confirm the changes.
terraform -chdir="${TF_DIR}" apply \
  -var="gcp_project_id=${GCP_PROJECT_ID}" \
  -var="image_digest=${FULL_IMAGE_DIGEST}"

echo "Done."
