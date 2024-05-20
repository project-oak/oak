extern crate prost_build;

fn main() {
    let mut config = prost_build::Config::new();
    config.btree_map(&["."]);
    prost_build::compile_protos(&["src/eventlog.proto"],
                                &["src/"]).unwrap();
}