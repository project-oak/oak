# Oak Verity

Oak Verity is a WebAssembly execution service that produces verifiable manifests
containing cryptographic digests of inputs, outputs, and executed code. It's
designed to be dual to Oak Functions, using the same ABI and infrastructure
while focusing on integrity rather than confidentiality.

## Overview

Oak Verity executes WebAssembly modules and returns both the execution output
and a manifest containing SHA-256 digests of:

- Input data
- WebAssembly module bytecode
- Output data

This enables independent verification of computations and forms the foundation
for attestable execution.

## Components

### Core Library (`oak_verity`)

- **Pure Rust library** with no main function
- **Reuses Oak Functions infrastructure** for Wasm execution
- **Manifest generation** with SHA-256 digests
- **Compatible ABI** - works with any Oak Functions-compatible Wasm module

### Command Line Interface (`oak_verity_cli`)

A simple CLI tool for executing WebAssembly modules and producing verifiable
manifests.

This is meant mostly for testing the Wasm module locally, as it does not produce
any attestation.

## Usage

### Building a Wasm Module

First, build a compatible Wasm module. For example, the echo module:

```bash
bazel build //oak_functions/examples/echo:echo
cp bazel-bin/oak_functions/examples/echo/echo.wasm /tmp/echo.wasm
```

We need to copy the module to a different location because the `bazel-bin`
symlink will be overridden by the next bazel invocation for a different
platform.

### Running the CLI

Execute a Wasm module with input data:

```bash
echo 'hello' > /tmp/input.txt

bazel run //oak_verity/cli:oak_verity_cli -- \
  --input-data=/tmp/input.txt \
  --wasm-module=/tmp/echo.wasm \
  --output-data=/tmp/output.txt
```

The CLI will:

1. Read the input data from `/tmp/input.txt`
2. Execute it through the specified Wasm module
3. Write the raw output data to `/tmp/output.txt`

### Inspecting the Output

If you used `--output-response`, you can pretty print the `ExecuteResponse`
protobuf using `protoc`:

```bash
protoc --decode=oak.verity.ExecuteResponse \
  proto/oak_verity/oak_verity.proto \
  < /tmp/response.binpb
```

Example output:

```text
manifest {
  input_data_digest {
    sha2_256: "\x12\x34\x56..."
  }
  wasm_module_digest {
    sha2_256: "\x78\x9a\xbc..."
  }
  output_data_digest {
    sha2_256: "\xde\xf0\x12..."
  }
}
output_data: "hello\n"
```

## WebAssembly Compatibility

Oak Verity is compatible with any WebAssembly module that follows the Oak
Functions ABI.

### Example Wasm Module (Rust)

```rust
use oak_functions_sdk;

#[no_mangle]
pub extern "C" fn main() {
    let request = oak_functions_sdk::read_request()
        .expect("couldn't read request");

    // Process the request data...
    let response = process_data(request);

    oak_functions_sdk::write_response(&response)
        .expect("couldn't write response");
}

fn process_data(input: Vec<u8>) -> Vec<u8> {
    // Your computation logic here
    input // Echo example
}
```
