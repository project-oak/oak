# Play Around Emojify

## Build

- Copy the latest or a specific version of `tranformer_expression.tflite` to
  this folder
- Build with debugging information without stripping symbols

  ```bash
  bazel build --copt=-g --strip=never //testing/tflite_micro/transformer_expression
  ```

## Debug Model Outputs

Apply the lldb configuration to `.vscode/launch.json`

```text
{
    // Use IntelliSense to learn about possible attributes.
    // Hover to view descriptions of existing attributes.
    // For more information, visit: https://go.microsoft.com/fwlink/?linkid=830387
    "version": "0.2.0",
    "configurations": [
        {
            "type": "lldb",
            "request": "launch",
            "name": "Debug",
            "program": "${workspaceFolder}/bazel-bin/testing/tflite_micro/transformer_expression/transformer_expression",
            "args": [],
            "cwd": "${workspaceFolder}",
            "sourceMap": {
                "/proc/self/cwd": "${workspaceFolder}",
            }
        }
    ]
}
```

Set breakpoint to `the line of code after tflite_run(...)` at main.cpp and press
F5 to start debugger that stops execution at the configured breakpoint.

Check the raw `float` content of `output` variable at `VARIABLES` window.

Notes:

- Optionally add `--define=no_opt=1` to bazel build command to prevent compiler
  optimizations such as changing or reordering control flows, etc if you'd like
  breakdowns taking effects at the exact code lines you set.

## Validate Model Outputs

The freestanding binary would iterate all test sets at
[testdata.c](https://github.com/project-oak/oak/blob/main/testing/tflite_micro/transformer_expression/testdata.c).

If N-th set of test data failed validation (which means model output is
inaccurate), N would be return from the main(). Simply reading the return value
from the shell can tell which test set failed validation.

A script is provided to build, run and validate model outputs of a Linux
freestanding binary, simply execute:

```bash
testing/tflite_micro/transformer_expression/test.sh
```

If all data sets passed validation, a `PASSED` will be shown on the console.
Otherwise, an error or failure reason i.e. N-th data set failed validation will
be shown instead.
