IMAGE_BINARIES_DIRECTORY := ./target/image_binaries

.PHONY: all clean

all: image.tar.xz

$(IMAGE_BINARIES_DIRECTORY):
		mkdir -p $(IMAGE_BINARIES_DIRECTORY)

# Build binaries
$(IMAGE_BINARIES_DIRECTORY)/oak_containers_orchestrator: $(IMAGE_BINARIES_DIRECTORY)
		cargo build --package=oak_containers_orchestrator --profile=release-lto --target=x86_64-unknown-linux-musl -Z unstable-options --out-dir=./target

$(IMAGE_BINARIES_DIRECTORY)/oak_containers_syslogd: $(IMAGE_BINARIES_DIRECTORY)
		cargo build --package=oak_containers_syslogd --release -Z unstable-options --out-dir=./target
		cp $< $@
		patchelf --set-interpreter /lib64/ld-linux-x86-64.so.2 $@

# Build system image
oak_containers_system_image.tar: $(IMAGE_BINARIES_DIRECTORY) $(IMAGE_BINARIES_DIRECTORY)/oak_containers_syslogd
		bazel build oak_containers_system_image

# Create compressed image archive
image.tar.xz: oak_containers_system_image.tar
		cp ../bazel-bin/oak_containers_system_image/oak_containers_system_image.tar ./target/image.tar
		xz --force target/image.tar

clean:
		rm -rf $(IMAGE_BINARIES_DIRECTORY) target/image.tar*
