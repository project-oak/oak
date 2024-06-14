all: target/bzImage

target/bzImage:
	mkdir --parents target
	# We just copy the prebuilt kernel from nix to the target folder.
	# We can probably simplify things a bit in the future.
	cp $${LINUX_KERNEL}/bzImage target/bzImage
	# Log digest of kernel in order to detect non reproducibility.
	sha256sum target/bzImage

target/vanilla_bzImage:
	mkdir --parents target
	cp $${VANILLA_LINUX_KERNEL}/bzImage target/vanilla_bzImage
	sha256sum target/vanilla_bzImage

clean:
	rm --recursive --force target
