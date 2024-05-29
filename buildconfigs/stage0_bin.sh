#!/bin/bash
#
# Build configuration for stage0_bin.
#
export PACKAGE_NAME=stage0_bin

export BUILD_COMMAND=(
  nix
  develop
  .#rust
  --command
  just
  stage0_provenance_subjects
)

# The first element must be the Transparent Release binary (the main binary).
export SUBJECT_PATHS=(
  stage0_bin/target/x86_64-unknown-none/release/stage0_bin
  stage0_bin/bin/subjects/sha2_384_measurement_of_initial_memory_with_stage0_and_01_vcpu
  stage0_bin/bin/subjects/sha2_384_measurement_of_initial_memory_with_stage0_and_02_vcpu
  stage0_bin/bin/subjects/sha2_384_measurement_of_initial_memory_with_stage0_and_04_vcpu
  stage0_bin/bin/subjects/sha2_384_measurement_of_initial_memory_with_stage0_and_08_vcpu
  stage0_bin/bin/subjects/sha2_384_measurement_of_initial_memory_with_stage0_and_16_vcpu
  stage0_bin/bin/subjects/sha2_384_measurement_of_initial_memory_with_stage0_and_32_vcpu
  stage0_bin/bin/subjects/sha2_384_measurement_of_initial_memory_with_stage0_and_64_vcpu
)
