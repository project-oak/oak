all: target/vmlinux

target/vmlinux: target/bzImage
	target/linux-6.7.6/scripts/extract-vmlinux  target/bzImage > target/vmlinux


target/bzImage: target/linux-6.7.6 configs/6.7.6/minimal.config
	KCONFIG_CONFIG=../../configs/6.7.6/minimal.config $(MAKE) -C target/linux-6.7.6 bzImage -j `nproc`
	cp target/linux-6.7.6/arch/x86/boot/bzImage target/bzImage

target/linux-6.7.6:
	mkdir -p target
	curl -O -L --output-dir target https://cdn.kernel.org/pub/linux/kernel/v6.x/linux-6.7.6.tar.xz
	tar -C target -Jxf target/linux-6.7.6.tar.xz
	patch -p1 -d target/linux-6.7.6 < patches/virtio-dma.patch
