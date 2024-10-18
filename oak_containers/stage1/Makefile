all: ../../target/stage1.cpio

# Always try to recompile the Rust binary.
.PHONY: ../../target/x86_64-unknown-linux-musl/release/oak_containers_stage1

../../target/stage1.cpio: ../../target/x86_64-unknown-linux-musl/release/oak_containers_stage1 ../../target/mke2fs
	cp ../../target/x86_64-unknown-linux-musl/release/oak_containers_stage1 ../../target/init
	echo -e "init\nmke2fs" | cpio -o -R root:root -H newc -v --reproducible -D ../../target > ../../target/stage1.cpio.tmp
	strip-nondeterminism --type cpio -T 0 ../../target/stage1.cpio.tmp
	gzip --best --no-name ../../target/stage1.cpio.tmp
	mv ../../target/stage1.cpio.tmp.gz ../../target/stage1.cpio

../../target/x86_64-unknown-linux-musl/release/oak_containers_stage1:
	cargo build --release --target x86_64-unknown-linux-musl
	strip ../../target/x86_64-unknown-linux-musl/release/oak_containers_stage1

../../target/mke2fs:
	bazel build @e2fsprogs//:mke2fs -c opt
	cp ../../bazel-bin/external/e2fsprogs/mke2fs/sbin/mke2fs ../../target/mke2fs
