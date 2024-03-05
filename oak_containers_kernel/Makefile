all: target/vmlinux

target/vmlinux: target/bzImage
	target/linux-6.7.6/scripts/extract-vmlinux target/bzImage > target/vmlinux

target/bzImage: target/linux-6.7.6 configs/6.7.6/minimal.config
	KCONFIG_CONFIG=../../configs/6.7.6/minimal.config $(MAKE) --directory=target/linux-6.7.6 bzImage --jobs=$$(nproc)
	cp target/linux-6.7.6/arch/x86/boot/bzImage target/bzImage

# LINUX_KERNEL_UPSTREAM is fetched by nix and pinned by its digest. See /flake.nix.
target/linux-6.7.6:
	mkdir -p target
	tar --directory=target --xz --extract --file=$${LINUX_KERNEL_UPSTREAM}
	patch -p1 -d target/linux-6.7.6 < patches/virtio-dma.patch
