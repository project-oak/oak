fn main() {
    protoc_rust_grpc::run(protoc_rust_grpc::Args {
        out_dir: "src/proto",
        input: &["../../proto/hello_world.proto"],
        includes: &["../../proto", "../../third_party"],
        rust_protobuf: true, // also generate protobuf messages, not just services
        ..Default::default()
    })
    .expect("protoc-rust-grpc");
}
