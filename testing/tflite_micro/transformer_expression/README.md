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

Set breakpoint to `return 0` at main.cpp and press F5 to start debugger that
stops execution at the configured breakpoint.

Check the raw `float` content of `output` variable at `VARIABLES` window.

Notes:

- `input` is set to `{"I", "love", "you"}` by default, change it accordingly to
  examine model outputs.
- Optionally add `--define=no_opt=1` to bazel build command to prevent compiler
  optimizations such as changing or reordering control flows, etc if you'd like
  breakdowns taking effects at the exact code lines you set.
