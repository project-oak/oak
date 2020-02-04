fn main() {
    oak_utils::run_protoc_rust(protoc_rust::Args {
        out_dir: "src/proto",
        input: &["../../../../oak/proto/oak_api.proto"],
        includes: &["../../../../oak/proto"],
        customize: protoc_rust::Customize::default(),
    })
    .expect("protoc");
}
