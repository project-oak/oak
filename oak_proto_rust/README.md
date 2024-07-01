# Oak Proto Rust Library

This is a transitional library that's serving as the single dependency to add
when you need to depend on any Oak protos from a Bazel build.

If the proto you need isn't yet build by this library, you can add it to the
build.rs file (and update the dependencies for the build script target as
needed.)

This library is imported into some environments where Prost and/or build scripts
are not available. To support building our Rust targets in these environmnets,
we also include pre-generated Prost Rust code in the `generated` directory.

The bazel `write_source_files` helps us with this. It creates a rule for copying
the generated files, as well as a rule that verifies that they exist in the
right place.

If proto changes are made, you should run:
`bazel run oak_proto_rust:copy_generated_files`

If you forget, your presubmit will fail, with a message telling you to run that
command.
