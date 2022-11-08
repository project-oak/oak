# TensorFlow Lite for Microcontroller (TLFM) on Oak

## File and Directory Structure

```text
cc
|-- tflite_micro
|   |-- include
|   |   Declare Oak tflite apis used by freestanding app binaries and Oak TensorFlow runtime.
|   |
|   |-- BUILD
|   |   Provide Oak-specific build options and shared headers/sources/deps
|   |   i.e. Oak DebugLog and TFLM-on-Oak library.
|   |
|   |-- build_defs.bzl
|   |   Provide Oak-specific compiler options, linker options and tool macros.
|   |
|   |-- debug_log.cc
|   |   Implement Oak-specific debug logging required by TFLM micro-printf.
|   |
|   |-- tflite_micro.cc
|   |   Implement generic tflite model runner.
|   |
|   |-- tools
|   |   |-- BUILD
|   |   |   Tool dep to convert tflite model to cc arrays in bazel build process.
|   |   |
|   |   |-- update_tflm.sh
|   |   |   Tool for upgrading/downgrading TFLM sources and dependencies.
|
|-- libc
|   A pico libc linked by TFLM and only required apis are implemented.
|   bsearch and optimized (by SIMD instruction set i.e. SSE2/SSSE3/SSE4/AVX2) string apis
|   are sourced and modified from Android bionic libc*.
|   misc.cc implements apis required by TFLM and releated/specific to Oak trusted execution environment.
|   Other sources are sourced from Google nanolibc**, which currently misses bsearch,
|   string-to-{float|double} and most apis are implemented in a highly non-optimized
|   way for better portability.
|
|-- libgcc
|   A pico libgcc implements clrsb GCC builtin function required by TFLM.
|
|-- libm
|   A pico libm implements a set of complementary math apis required by TFLM.
|
|   For freestanding model app binaries running on Linux, compiler links static libm by default (-lm)
|   to pull in required math apis in addition to the math apis supplemented by this libm.
|
|   For freestanding model app binaries running in Oak server, rustc compiler would pull in required
|   math apis from Oak libm.rs in addition to the math apis supplemented by this libm.

testing
|-- tflite_micro
|   All tflite model apps are put under this folder.
|   |-- hello_world
|   |   hello_world tflite model app.
|   |
|   |-- BUILD
|   |   Provide common dependencies shared by all tflite model apps.
|   |
|   |-- start.S
|   |   Used by tflite model apps to generate freestanding and executable binary
|   |   to run on Linux.
```

\*
[Android bionic libc](https://android.googlesource.com/platform/bionic/+/refs/heads/master)\
\*\* [Google nanolibc](https://github.com/google/nanolibc)

## Upgrade/Downgrade TFLM

We generate a clean set of TFLM source tree via its built-in tool
[create_tflm_tree.py](https://github.com/tensorflow/tflite-micro/blob/main/tensorflow/lite/micro/tools/project_generation/create_tflm_tree.py)
that cuts ~50% sources to be compiled, which also implies fewer external
dependency errors to fix in a freestanding binary development environment.

The generated source tree consists of TFLM sources and required third-party
headers. As we want generated TFLM sources residing in the
third_party/tflite-micro directory and its third-party dependencies also
residing in respective directories under the third_party, corresponding BUILD
files consolidating file groups of sources and headers are needed for each of
them to be properly depended by the tflite_micro terminal target at
cc/tflite_micro/BUILD.

Given its complexity of cleanly upgrading/downgrading sources, in the meanwhile,
keeping our own BUILD files intact, a handy tool script is provided to simplify
TFLM upgrade/downgrade process:

```bash
# Step 1: sync TFLM to tot or a specific commit for upgrade/downgrade

# Step 2: use update_tflm.sh to upgrade/downgrade TFLM sources cleanly
# TFLM_SOURCE_ROOT_PATH is the root path of cloned https://github.com/tensorflow/tflite-micro
# Both absolute path and relative path are supported.
cc/tflite_micro/tools/update_tflm.sh TFLM_SOURCE_ROOT_PATH

# Step 3: commit updates by git add third_party/tflite-micro; git commit; git push

# Step 4: send the PR for review
```

## Build Model Binaries

There are two sorts of freestanding binaries, using hello_world model app as
example:

1. Build the binary that runs on Linux

   ```bash
   bazel build //testing/tflite_micro/hello_world:hello_world_freestanding_bin
   ```

   The binary is built with -nostdlib which removes dependencies of standard
   libraries i.e. libc, libgcc, etc to ensure a freestanding binary is generated
   and can run on Linux. The binary is good for tflite model porting, debugging
   and tensor activation validating. Its freestanding nature makes it a good fit
   of validating execution on TEE.

1. Binaries that runs on Oak server
   ```bash
   cd oak_tensorflow_freestanding_bin
   cargo build
   ```
   The binary is built with Oak Restricted Kernel and Oak TensorFlow Service,
   which can be loaded into virtual machine for execution under TEE.

### Additional Build Options

There are few optional build options provided:

- `--define=no_opt=1`

  Disable compiler optimizations when building model app freestanding binaries.

- `--define=no_sse=1`

  Disable using streaming SIMD instructions i.e. SSE2/SSSE3/SSE4/AVX2. The
  option under the hook would use non-optimized nanolibc string apis i.e.
  str{len|cmp|cpy|...}, mem{cpy|cmp|move|set|...}, etc. Additionally, tflite is
  built without `-msse4.2`.

- `--define=use_custom_output=1`

  The option is specific to hello_world Linux freestanding binary. It builds
  hello_world Linux freestanding binary without using Oak debug_log.cc; instead,
  using a custom debug_log.cc for use cases i.e. testing, ported to other
  operating systems that implement proprietary debug logging, etc.

## Debugging Model Binaries

As aforementioned, we are able to build freestanding libraries that can run on
Linux. In order for debugger i.e. gdb/lldb to correctly work on the binaries, we
need to specify additional build parameters telling bazel to keep all debug
symbols and optionally disabling optimizations so breakpoints can be precisely
mapped to correct lines of source code.

Use hello_world model app as example,

```bash
bazel build --copt=-g --strip=never --define=no_opt=1 //testing/tflite_micro/hello_world:hello_world_freestanding_bin
```

`--define=no_opt=1` is optional if correct source mapping is not needed.

Next, configure i.e. lldb for VS Code,

.vscode/launch.json

```json
{
  "version": "0.2.0",
  "configurations": [
    {
      "type": "lldb",
      "request": "launch",
      "name": "Debug",
      "program": "${workspaceFolder}/bazel-bin/testing/tflite_micro/hello_world/hello_world_freestanding_bin",
      "args": [],
      "cwd": "${workspaceFolder}",
      "sourceMap": {
        "/proc/self/cwd": "${workspaceFolder}"
      }
    }
  ]
}
```

As bazel replaces the actual source location with `/proc/self/cwd` to achieve
reproducible builds, it is required to add the mapping
`"/proc/self/cwd": "${workspaceFolder}"`.

After applying the configuration, you are good to go to set breakpoints in
sources, watch memory contents, online memory/register manipulations and so
forth.
