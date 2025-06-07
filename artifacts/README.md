# Artifacts output location

This is a common holding spot for generated build artifacts that will be used
outside of Bazel. Please place things in this directory rather than using one
of the various `target` or `generated` directories.

The directory structure here is important, and matches some internal
definitions (go/go/oak-kokoro-artifacts-cfg). Please only add artifacts to one
of the pre-defined sub-directories here, *not* to the top-level.
