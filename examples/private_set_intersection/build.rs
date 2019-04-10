extern crate protoc_rust;

fn main() {
    protoc_rust::run(protoc_rust::Args {
        out_dir: "src/proto",
        input: &["proto/private_set_intersection.proto"],
        includes: &[],
        customize: protoc_rust::Customize::default(),
    })
    .expect("protoc");
}
