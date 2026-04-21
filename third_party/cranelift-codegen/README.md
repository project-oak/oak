# Cranelift Codegen Patch

This directory contains a patch for the `cranelift-codegen` crate to address issues when building with Bazel in a sandboxed environment.

## Problem

During the build process, `cranelift-codegen` executes a build script (`build.rs`) that generates Rust code from ISLE files. The paths to these ISLE files are passed to the build script from previous build actions (e.g., from `cranelift-assembler-x64`).

In a Bazel sandboxed environment, these paths often include absolute paths that reference the specific sandbox directory of the *previous* action (e.g., `/.../sandbox/linux-sandbox/123/execroot/...`). When the current action tries to read these files in its own sandbox (e.g., `/.../sandbox/linux-sandbox/456/execroot/...`), it fails because the path points to a non-existent directory.

## Solution

The patch in `patch_build_rs.patch` modifies `build.rs` to:
1.  Extract the current sandbox root path up to `execroot/_main/` from the current working directory.
2.  For each input file path, if it contains `execroot/_main/`, it strips the old sandbox prefix and resolves the remainder of the path relative to the *current* sandbox root.

This ensures that paths generated in previous actions are correctly mapped to the current sandbox environment.

## Usage

The patch is applied via `crate.annotation` in `MODULE.bazel`.
