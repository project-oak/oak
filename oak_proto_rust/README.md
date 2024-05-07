# Oak Proto Rust Library

This is a transitional library that's serving as the single dependency to add
when you need to depend on any Oak protos from a Bazel build.

If the proto you need isn't yet build by this library, you can add it to the
build.rs file (and update the dependencies for the build script target as
needed.)

This library is imported into some environments where Prost and/or build scripts
are not available. To support building our Rust targets in these environmnets,
we also include pre-generated Prost Rust code in the `generated` directory.

A presubmit job will run the `oak_proto_rust:verify_generated` target to verify
that all generated code also exists in the `generated` directory.

If proto changes are made, you should run:

`blaze run oak_proto_rust:copy_generated`

to copy any added/modified files. Not that the script will not cover any
_removed_ files, so take care to clean up any uneeded files if protos are
removed at some point.
