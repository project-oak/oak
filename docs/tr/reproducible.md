# Reproducible builds of Oak binaries

The following table shows the reproducibility status for each Oak binary, where
we consider it sufficient to have two independent builds (Kokoro and GitHub)
including provenances and yielding a bitwise identical binary. This condition is
continuously monitored for regressions.

| Package name                                        | Reproducibility | Comment                   |
| --------------------------------------------------- | --------------- | ------------------------- |
| key_xor_test_app                                    | Yes             |                           |
| oak_containers_kernel                               | Yes             |                           |
| oak_containers_stage1                               | Yes             |                           |
| oak_containers_system_image                         | Yes             |                           |
| oak_echo_enclave_app                                | Yes             |                           |
| oak_echo_raw_enclave_app                            | Yes             |                           |
| oak_functions_container                             | No              | GitHub provenance missing |
| oak_functions_enclave_app                           | Yes             |                           |
| oak_functions_insecure_container                    | No              | GitHub provenance missing |
| oak_functions_insecure_enclave_app                  | Yes             |                           |
| oak_restricted_kernel_simple_io_init_rd_wrapper_bin | Yes             |                           |
| oak_orchestrator                                    | Yes             |                           |
| stage0_bin                                          | Yes             |                           |
| stage0_bin_tdx                                      | Yes             |                           |
