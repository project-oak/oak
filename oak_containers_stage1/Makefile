all: ../target/stage1.cpio

# Always try to recompile the Rust binary.
.PHONY: ../target/x86_64-unknown-linux-musl/release/oak_containers_stage1

../target/stage1.cpio: ../target/x86_64-unknown-linux-musl/release/oak_containers_stage1 ../target/tar
	cp ../target/x86_64-unknown-linux-musl/release/oak_containers_stage1 ../target/init
	echo "init\ntar" | cpio -o -R root:root -H newc -v --reproducible -D ../target | gzip -9 > ../target/stage1.cpio

../target/x86_64-unknown-linux-musl/release/oak_containers_stage1:
	cargo build --release --target x86_64-unknown-linux-musl
	strip ../target/x86_64-unknown-linux-musl/release/oak_containers_stage1

../target/tar:
	mkdir -p target
	curl -O -L --output-dir target https://ftpmirror.gnu.org/tar/tar-1.34.tar.xz
	tar -C target -Jxf target/tar-1.34.tar.xz
	cd target/tar-1.34 && ./configure LDFLAGS="-static" FORCE_UNSAFE_CONFIGURE=1
	$(MAKE) -C target/tar-1.34 -j `nproc`
	strip target/tar-1.34/src/tar
	cp target/tar-1.34/src/tar ../target/tar
