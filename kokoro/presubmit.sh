#!/usr/bin/env bash

./scripts/docker_pull

ls -l /dev/kvm
sudo chwon "$USER" /dev/kvm
ls -l /dev/kvm
./scripts/docker_run ls -l /dev/kvm

./scripts/docker_run ./scripts/xtask build-oak-functions-server-variants
./scripts/docker_run ./scripts/xtask run-vm-test
