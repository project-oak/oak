# `oak_lint_runner`

`oak_lint_runner` is a concurrent, language-aware lint runner for the Project
Oak repository. It executes multiple linting and formatting tools (such as
`rustfmt`, `clang-format`, `shfmt`, `buildifier`, and `prettier`) in parallel.

## Features

- **Concurrency:** Uses `tokio` to run linting tasks in parallel.
- **Batched Executions:** Groups files in configurable batches (defaulting to 50
  files per batch) to reduce process-spawning overhead.
- **File Detection:** Uses `tokei` and `content_inspector` to evaluate file
  types based on extensions, content, and shebangs.
- **Configurable:** Driven by a `.oak-lint-config.toml` file that maps tools to
  their commands and supported file types.
- **Output:** Summarizes successful, failed, and skipped tools, and prints
  `stdout`/`stderr` from failing tools.

## Configuration

The runner reads `.oak-lint-config.toml` by default. An example configuration
block for a tool looks like this:

```toml
[tools.shfmt]
name = "shfmt (shell script files)"
entry = "shfmt --indent=2 --case-indent --write"
types = ["bash"]
```

Tools can filter files by `types` (e.g., `rust`, `cpp`, `bash`, `bazel`,
`yaml`), explicitly matched `files` (regex on path names), or specifically
ignored using `exclude` regexes.

## Usage

```bash
# Run all configured tools on a specific file
bazel run //tools/lint-runner:oak_lint_runner -- path/to/file.rs

# Typically used alongside scripts that pipe changed files
git diff --name-only main | bazel run //tools/lint-runner:oak_lint_runner --

# Or via the wrapper script (which handles Bazel compilation and piping changed files)
./tools/lint-runner/scripts/format_changed
```

### Advanced Usage

```bash
oak_lint_runner [OPTIONS] [FILES]...

Arguments:
  [FILES]...  List of files to run the linting tools on (or via stdin)

Options:
      --config <CONFIG>        Path to the configuration file [default: .oak-lint-config.toml]
  -j, --jobs <JOBS>            Maximum number of concurrent tool executions
  -b, --batch-size <SIZE>      Number of files to process in a single tool execution batch [default: 50]
  -t, --tool <TOOL>            Optional ID of a single tool to run
  -h, --help                   Print help
```
