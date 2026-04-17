
default:
    @just --list containers

# Update and build the Oak Containers system image
system-image:
    ./oak_containers/system_image/base/build-base.sh vanilla

# Update and build the Oak Containers system image with nvidia GPU support
nvidia-system-image:
    ./oak_containers/system_image/base/build-base.sh nvidia

# Update and rebuild the Oak Containers sysroot.
[working-directory: "../oak_containers/sysroot"]
sysroot:
    bazel run @sysroot//:lock
    bazel build sysroot

[working-directory: "../oak_containers/sysroot"]
sysroot-dev:
    bazel run @sysroot//:lock
    bazel build sysroot-dev
    @printf "\nAbsolute Location:\n\n  $(pwd)/bazel-bin/sysroot-dev.tar\n\n"

push-system-image:
    ./oak_containers/system_image/base/push-base.sh vanilla
push-nvidia-system-image:
    ./oak_containers/system_image/base/push-base.sh nvidia

[working-directory: "../oak_containers/sysroot"]
push-sysroot:
    bazel run @sysroot//:lock
    bazel build sysroot
    bazel run push
