extern crate protoc_rust;

fn main() {
    protoc_rust::run(protoc_rust::Args {
        out_dir: "src/proto",
        input: &["proto/hello_world.proto"],
        includes: &[],
        customize: protoc_rust::Customize::default(),
    })
    .expect("protoc");
}
