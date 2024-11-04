all: ../../target/stage1.cpio

# Always try to recompile the Rust binary.
.PHONY: ../../target/stage1/init

../../target/stage1.cpio: ../../target/stage1/init ../../target/stage1/mke2fs ../../target/stage1/lib64 ../../target/stage1/usr/lib/x86_64-linux-gnu
	(cd ../../target/stage1 && find .) | cpio -o -R root:root -H newc -v --reproducible -D ../../target/stage1 > ../../target/stage1.cpio.tmp
	strip-nondeterminism --type cpio -T 0 ../../target/stage1.cpio.tmp
	gzip --best --no-name ../../target/stage1.cpio.tmp
	mv ../../target/stage1.cpio.tmp.gz ../../target/stage1.cpio

# Stage 1 binary (init process).
../../target/stage1/init:
	bazel build //oak_containers/stage1
	mkdir --parents ../../target/stage1
	strip ../../bazel-bin/oak_containers/stage1/oak_containers_stage1 -o ../../target/stage1/init

# Dynamic linker.
../../target/stage1/lib64:
	bazel build //oak_containers/stage1:copy_shared_libraries
	mkdir --parents ../../target/stage1/lib64
	cp -f ../../bazel-bin/oak_containers/stage1/shared_libraries/ld-linux-x86-64.so.2 ../../target/stage1/lib64/

# Shared libraries.
../../target/stage1/usr/lib/x86_64-linux-gnu:
	bazel build //oak_containers/stage1:copy_shared_libraries
	mkdir --parents ../../target/stage1/usr/lib/x86_64-linux-gnu
	cp ../../bazel-bin/oak_containers/stage1/shared_libraries/libgcc_s.so.1 ../../target/stage1/usr/lib/x86_64-linux-gnu/
	cp ../../bazel-bin/oak_containers/stage1/shared_libraries/libm.so.6 ../../target/stage1/usr/lib/x86_64-linux-gnu/
	cp ../../bazel-bin/oak_containers/stage1/shared_libraries/libc.so.6 ../../target/stage1/usr/lib/x86_64-linux-gnu/

# Filesystem creation helper tool.
../../target/stage1/mke2fs:
	bazel build @e2fsprogs//:mke2fs -c opt
	cp ../../bazel-bin/external/e2fsprogs/mke2fs/sbin/mke2fs ../../target/stage1/mke2fs
