#!/bin/bash
#
# Build configuration for oak_ml_transparency.
#
export PACKAGE_NAME=oak_ml_transparency

export BUILD_COMMAND=(
  env
  --chdir=oak_ml_transparency/mnist
  /project/runner-musl
  --model=/project/mnist_model.tar.gz
  --model-name=mnist
  --eval-script=/project/eval.py
  --output=claim.json
)

export BINARY_PATH=oak_ml_transparency/mnist/claim.json
export SUBJECT_PATH="${BINARY_PATH}"
