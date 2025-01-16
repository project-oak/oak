# Getting Started

This directory contains a minimal template for writting enclave apps with `oak`.

## Usage

1. Install `Nix` as instructed in
   [oak development guide](https://github.com/project-oak/oak/blob/82caf8d91a6397b065f4ad9520b60415b39d8a73/docs/development.md).
2. Copy this template directory.
3. Enter the development environment: `nix develop`
4. Build the enclave application: `bazel build //enclave_app:enclave_app`
