#!/bin/bash

TIME_SUFFIX="$(date +"%F-%H-%M")"
PROJECT_ID="oak-functions-standalone"
REPOSITORY_NAME="oak-functions-standalone-containers"
WASM_URL="https://storage.googleapis.com/oak-functions-standalone-bucket/wasm/key_value_lookup.wasm"
LOOKUP_DATA_URL="https://storage.googleapis.com/oak-functions-standalone-bucket/lookup_data/fake_weather_data.binarypb"

gcloud auth login

bazel run //oak_functions_standalone:oak_functions_standalone_load_image

docker tag \
  oak_functions_standalone:latest \
  europe-west1-docker.pkg.dev/${PROJECT_ID}/${REPOSITORY_NAME}/oak_functions_standalone:latest

docker push europe-west1-docker.pkg.dev/${PROJECT_ID}/${REPOSITORY_NAME}/oak_functions_standalone:latest

instance_name="${PROJECT_ID}-debug-${TIME_SUFFIX}"

echo "Launching container instance on Confidential Space as: ${instance_name}"

gcloud compute instances create "${instance_name}" \
  --confidential-compute-type=TDX \
  --image-project=confidential-space-images \
  --image-family=confidential-space \
  --maintenance-policy=TERMINATE \
  --shielded-secure-boot \
  --metadata="^~^tee-image-reference=europe-west1-docker.pkg.dev/${PROJECT_ID}/${REPOSITORY_NAME}/oak_functions_standalone:latest~tee-container-log-redirect=true~tee-cmd=[\"--wasm-uri=${WASM_URL}\",\"--lookup-data-uri=${LOOKUP_DATA_URL}\",\"--attestation-type=self-unidirectional\"]" \
  --scopes=cloud-platform \
  --zone=us-west1-b

echo "Containers image successfully tagged and pushed. Check pantheon for running job."
