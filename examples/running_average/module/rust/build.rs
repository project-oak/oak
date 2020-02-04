fn main() {
    oak_utils::run_protoc_rust_grpc(protoc_rust_grpc::Args {
        out_dir: "src/proto",
        input: &["../../proto/running_average.proto"],
        includes: &["../../proto"],
        rust_protobuf: true, // also generate protobuf messages, not just services
        ..Default::default()
    })
    .expect("protoc-rust-grpc");
}
