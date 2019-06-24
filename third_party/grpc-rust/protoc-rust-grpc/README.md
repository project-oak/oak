# API to generate .rs files

API to generate .rs files to be used e. g.
[from `build.rs`](https://github.com/stepancheg/grpc-rust/blob/master/interop/build.rs).

Example code:

```rust
extern crate protoc_rust_grpc;

fn main() {
    protoc_rust_grpc::run(protoc_rust_grpc::Args {
        out_dir: "src",
        includes: &["proto"],
        input: &["proto/aaa.proto", "proto/bbb.proto"],
        rust_protobuf: true, // also generate protobuf messages, not just services
        ..Default::default()
    }).expect("protoc-rust-grpc");
}
```

Note this API requires protoc command present in `$PATH`.
Although `protoc-gen-rust-grpc` command is not needed.
