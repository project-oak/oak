# Evidence Verification Demo

This demo reproducably builds the entire software stack powering the deployment
of an Oak Enclave Application (firmware, kernel, application) from source code.
The build artifacts are measured.

The resulting measurements are then used to verify DICE attestation evidence
returned by a prior deployment of this Oak Enclave Application in a genuine AMD
SEV-SNP TEE.

Matching the measurements of the local builds with those found in the
attestation evidence makes it possible to trace the deployment all the way back
to (public) source code. This permits clients/users to make informed choices
about which workloads to connect to.

## Prerequisites

- Docker must be installed

## Running the demo

```sh
# First, pull the relevant builder docker image.
./scripts/docker_pull

# Second, start the docker container and enter the build shell.
./scripts/docker_run bash -c "nix develop"

# Lastly, run the demo script.
./demo_oc3_2024/get_measurements
```
