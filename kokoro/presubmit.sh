#!/usr/bin/env bash

./scripts/docker_pull
./scripts/docker_run ./scripts/xtask build-oak-functions-server-variants
./scripts/docker_run ./scripts/xtask run-vm-test
