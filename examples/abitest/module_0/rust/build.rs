fn main() {
    oak_utils::run_protoc_rust_grpc(protoc_rust_grpc::Args {
        out_dir: "src/proto",
        input: &["../../proto/abitest.proto"],
        includes: &["../../proto", "../../../../third_party"],
        rust_protobuf: true, // also generate protobuf messages, not just services
        ..Default::default()
    })
    .expect("protoc-rust-grpc");
}
