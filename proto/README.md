# Oak Protobuf Definitions

Source Protocol Buffer definitions for Project Oak.

## Overview

This directory contains the `.proto` files that define the messages and services
used for communication between various Oak components. These definitions are
used to generate code in multiple languages (primarily Rust and C++).

## Code Generation

The Rust code corresponding to these protos is generated in the `oak_proto_rust`
crate. If you modify any files in this directory, you must regenerate the Rust
code by running:

```bash
bazel run oak_proto_rust:copy_generated_files
```

C++ code generation is handled automatically by the Bazel build rules.
