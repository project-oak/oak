#!/bin/bash
#
# Build configuration for stage0_bin.
#
export PACKAGE_NAME=stage0_bin

export BUILD_COMMAND=(
  nix
  develop
  .#githubBuildShell
  --command
  just
  stage0_bin
)

# The first element must be the Transparent Release binary (the main binary).
export SUBJECT_PATHS=(
  artifacts/stage0_bin
  artifacts/stage0_bin_subjects/sha2_384_measurement_of_initial_memory_with_stage0_and_01_vcpu
  artifacts/stage0_bin_subjects/sha2_384_measurement_of_initial_memory_with_stage0_and_02_vcpu
  artifacts/stage0_bin_subjects/sha2_384_measurement_of_initial_memory_with_stage0_and_04_vcpu
  artifacts/stage0_bin_subjects/sha2_384_measurement_of_initial_memory_with_stage0_and_08_vcpu
  artifacts/stage0_bin_subjects/sha2_384_measurement_of_initial_memory_with_stage0_and_16_vcpu
  artifacts/stage0_bin_subjects/sha2_384_measurement_of_initial_memory_with_stage0_and_32_vcpu
  artifacts/stage0_bin_subjects/sha2_384_measurement_of_initial_memory_with_stage0_and_64_vcpu
)
