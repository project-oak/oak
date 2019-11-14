fn main() {
    protoc_rust::run(protoc_rust::Args {
        out_dir: "src/proto",
        input: &[
            "../../third_party/google/rpc/code.proto",
            "../../third_party/google/rpc/status.proto",
            "../../oak/proto/grpc_encap.proto",
            "../../oak/proto/oak_api.proto",
            "../../oak/proto/storage.proto",
            "../../oak/proto/storage_channel.proto",
        ],
        includes: &["../../oak/proto", "../.."],
        customize: protoc_rust::Customize::default(),
    })
    .expect("protoc");
}
