# Micro RPC Workspace Test

This directory contains a manual test to check whether the `micro_rpc` crate can
be depended on from a crate in another workspace.

See https://github.com/project-oak/oak/issues/4573 for context.

This crate overwrites the `WORKSPACE_ROOT` env variable with an invalid value in
the `.cargo/config.toml` file, which is necessary to shadow the corresponding
one in the root of this repository, to simulate an external workspace that would
not have that env variable set.

To reproduce the issue, run the following command from the repository root:

```bash
env --chdir=./micro_rpc_workspace_test bash -c 'cargo clean && cargo test'
```

If the issue is present, this will error out with something like

```text
  process didn't exit successfully: `/home/tzn/src/oak/micro_rpc_workspace_test/target/debug/build/micro_rpc-e60764e369835bbd/build-script-build` (exit status: 101)
  --- stdout
  cargo:rerun-if-changed=/home/tzn/src/oak/micro_rpc_workspace_test/_INVALID_WORKSPACE_ROOT_proto/micro_rpc/messages.proto

  --- stderr
  thread 'main' panicked at /home/tzn/src/oak/micro_rpc_build/src/lib.rs:91:10:
  couldn't compile protobuffer schema: Custom { kind: Other, error: "protoc failed: Could not make proto path relative: /home/tzn/src/oak/micro_rpc_workspace_test/_INVALID_WORKSPACE_ROOT_proto/micro_rpc/messages.proto: No such file or directory\n" }
  note: run with `RUST_BACKTRACE=1` environment variable to display a backtrace
```
