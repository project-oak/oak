extern crate grpc_compiler;

use grpc_compiler::codegen;

fn main() {
    codegen::protoc_gen_grpc_rust_main();
}
