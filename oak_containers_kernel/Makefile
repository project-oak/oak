all: target/vmlinux

target/vmlinux: target/bzImage target/linux-6.1.33
	target/linux-6.1.33/scripts/extract-vmlinux target/bzImage > target/vmlinux

target/bzImage:
	mkdir --parents target
	cp $${LINUX_KERNEL}/bzImage target/bzImage
	# Log digest of kernel in order to detect non reproducibility.
	sha256sum target/bzImage

# LINUX_KERNEL_SRC is fetched by nix and pinned by its digest. See /flake.nix.
# The only reason we still need the source available is that we need the `extract-vmlinux` script above.
target/linux-6.1.33:
	mkdir --parents target
	tar --directory=target --xz --extract --file=$${LINUX_KERNEL_SRC}

clean:
	rm --recursive --force target
