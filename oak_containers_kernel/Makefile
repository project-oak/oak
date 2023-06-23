all: target/vmlinux-6.3.9

target/vmlinux-6.3.9: target/linux-6.3.9/arch/x86/boot/bzImage
	target/linux-6.3.9/scripts/extract-vmlinux  target/linux-6.3.9/arch/x86/boot/bzImage > target/vmlinux-6.3.9

target/linux-6.3.9/arch/x86/boot/bzImage: target/linux-6.3.9/.config
	$(MAKE) -C target/linux-6.3.9 bzImage -j `nproc`

target/linux-6.3.9/.config: target/linux-6.3.9 configs/6.3.9/minimal.config
	cp configs/6.3.9/minimal.config target/linux-6.3.9/.config

target/linux-6.3.9:
	mkdir -p target
	curl -O -L --output-dir target https://cdn.kernel.org/pub/linux/kernel/v6.x/linux-6.3.9.tar.xz
	tar -C target -Jxf target/linux-6.3.9.tar.xz
