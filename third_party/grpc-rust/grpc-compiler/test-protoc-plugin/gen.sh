#!/bin/sh -e

cd $(dirname $0)

(
    cd ..
    cargo build
)

root=$(cd ../..; pwd)

PATH="$root/target/debug:$PATH"

protoc --rust_out=src fgfg.proto
protoc --rust-grpc_out=src fgfg.proto
