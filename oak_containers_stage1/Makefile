all: ../target/stage1.cpio

# Always try to recompile the Rust binary.
.PHONY: ../target/x86_64-unknown-linux-musl/release/oak_containers_stage1

../target/stage1.cpio: ../target/x86_64-unknown-linux-musl/release/oak_containers_stage1
	cp ../target/x86_64-unknown-linux-musl/release/oak_containers_stage1 ../target/init
	echo "init" | cpio -o -R root:root -H newc -v --reproducible -D ../target | gzip -9 > ../target/stage1.cpio

../target/x86_64-unknown-linux-musl/release/oak_containers_stage1:
	cargo build --release --target x86_64-unknown-linux-musl
