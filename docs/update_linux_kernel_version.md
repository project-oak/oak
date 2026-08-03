# Check for new releases of current LTS kernel we are using for Oak Containers

If a new version of the Linux LTS kernel has been released, we should update the
Linux kernel version for Oak Containers.

Such an update sometimes causes our kernel patches to fail, so the patches must
be updated to apply cleanly and match the new kernel version.

- **Note**: At the moment Debian 13 (which we use for the container system
  images and our compiler system) uses the 6.12 LTS branch of the Linux kernel,
  so we should stay on the latest version of the 6.12 LTS branch until we change
  to a Debian version that uses a different kernel version.
  - See list of releases at
    [https://cdn.kernel.org/pub/linux/kernel/v6.x/](https://cdn.kernel.org/pub/linux/kernel/v6.x/)

> **IMPORTANT: Avoiding Workspace & Jujutsu (`jj`) Pollution**  
> Do **NOT** download, extract, or build kernel sources inside the repository
> working tree (`<oak_path>`).  
> Extracting ~170,000 Linux kernel files inside the repo directory causes
> Jujutsu (`jj`) and Git to snapshot untracked files, resulting in severe
> performance slowdowns or snapshot failures (`snapshot.max-new-file-size`).  
> Always use a temporary directory outside the repository (e.g.,
> `/tmp/kernel-update`).
>
> **Note for AI Agents & Developers:**  
> If build tools like `bazel` or `just` fail or are missing dependencies in your
> local shell environment, try wrapping them in the Nix dev environment:
> `nix develop --command <command>` (e.g.,
> `nix develop --command just bazel-lockfile-all`).

---

## Example: Updating from 6.12.95 to 6.12.101

### 1. Update the kernel version in `<oak_path>/oak_containers/kernel/kernel_version.txt`

Write the new kernel version string (e.g. `6.12.101`):

```shell
echo "6.12.101" > oak_containers/kernel/kernel_version.txt
```

### 2. Download kernel source tarball to `/tmp` and update `kernel-common.nix`

Download the source tarball to `/tmp` and compute its SHA256 digest:

```shell
export KERNEL_VERSION=$(cat oak_containers/kernel/kernel_version.txt)
wget --output-document=/tmp/linux-${KERNEL_VERSION}.tar.xz https://cdn.kernel.org/pub/linux/kernel/v6.x/linux-${KERNEL_VERSION}.tar.xz
sha256sum /tmp/linux-${KERNEL_VERSION}.tar.xz
```

Update the expected SHA2-256 digest of the kernel source tarball in
`<oak_path>/oak_containers/kernel/kernel-common.nix`:

```nix
  src = builtins.fetchurl {
    url = "https://cdn.kernel.org/pub/linux/kernel/v6.x/linux-${linux_version}.tar.xz";
    sha256 = "<NEW_SHA256_DIGEST>";
  };
```

### 3. Update the configuration path under `<oak_path>/oak_containers/kernel/configs`

Rename the config directory to match the new version:

```shell
mv oak_containers/kernel/configs/6.12.95 oak_containers/kernel/configs/6.12.101
```

### 4. Update the configuration path in `<oak_path>/oak_containers/kernel/internal/extensions.bzl`

Update references from the old version to the new version in `nix_file_deps`:

```starlark
    nixpkgs_package(
        name = "nix_vanilla_linux_kernel",
        build_file_content = "exports_files([\"bzImage\"])",
        nix_file = "//oak_containers/kernel:vanilla-kernel.nix",
        nix_file_deps = [
            "//oak_containers/kernel:kernel-common.nix",
            "//oak_containers/kernel:kernel_version.txt",
            "//oak_containers/kernel/configs/6.12.101:minimal.config",
        ],
        repository = "@nixpkgs",
    )

    nixpkgs_package(
        name = "nix_linux_kernel",
        build_file_content = "exports_files([\"bzImage\"])",
        nix_file = "//oak_containers/kernel:kernel.nix",
        nix_file_deps = [
            "//oak_containers/kernel:kernel-common.nix",
            "//oak_containers/kernel:kernel_version.txt",
            "//oak_containers/kernel/configs/6.12.101:minimal.config",
            "//oak_containers/kernel/patches:virtio-dma.patch",
            "//oak_containers/kernel/patches:tdx-probe-roms.patch",
            "//oak_containers/kernel/patches:rtmr-enable.patch",
        ],
        repository = "@nixpkgs",
    )
```

### 5. Update the minimal kernel configuration file

Extract the kernel source into a temporary directory outside the repo and run
`make ARCH=x86_64 olddefconfig` to non-interactively refresh default values for
any new configuration symbols:

```shell
export WORK_DIR=/tmp/kernel-update-work
mkdir --parents ${WORK_DIR}
tar --directory=${WORK_DIR} --extract --file=/tmp/linux-${KERNEL_VERSION}.tar.xz

# Copy minimal.config to the source tree and update options
cp oak_containers/kernel/configs/${KERNEL_VERSION}/minimal.config ${WORK_DIR}/linux-${KERNEL_VERSION}/.config
make --directory=${WORK_DIR}/linux-${KERNEL_VERSION} ARCH=x86_64 olddefconfig

# Copy updated config back to the Oak repository
cp ${WORK_DIR}/linux-${KERNEL_VERSION}/.config oak_containers/kernel/configs/${KERNEL_VERSION}/minimal.config
```

### 6. Verify and update kernel patches under `<oak_path>/oak_containers/kernel/patches`

Test whether existing patches apply cleanly against the extracted source in
`${WORK_DIR}/linux-${KERNEL_VERSION}`:

```shell
cd ${WORK_DIR}/linux-${KERNEL_VERSION}

# Dry-run patch check
patch --strip=1 --dry-run < <oak_path>/oak_containers/kernel/patches/rtmr-enable.patch
patch --strip=1 --dry-run < <oak_path>/oak_containers/kernel/patches/tdx-probe-roms.patch
patch --strip=1 --dry-run < <oak_path>/oak_containers/kernel/patches/virtio-dma.patch
```

If a patch fails to apply cleanly:

1. Initialize a temporary git repository in
   `${WORK_DIR}/linux-${KERNEL_VERSION}`
   (`git init && git add . && git commit --message="pristine"`).
2. Manually apply the patch and resolve any merge conflicts.
3. Export the updated patch:
   `git diff > <oak_path>/oak_containers/kernel/patches/<patch_name>.patch`.

Clean up `/tmp/kernel-update-work` after verification.

### 7. Update Bazel lock files

```shell
just bazel-lockfile-all
```

### 8. Regenerate expected kernel sha256 digests

```shell
bazel run //oak_containers/kernel:regenerate_sha256
```

### 9. Update and push system images and sysroot

If required for the update, rebuild and push container images.

> **Note:** If Docker fails with `client version X.XX is too new`, set
> `export DOCKER_API_VERSION=1.41` before running `just containers ...`
> commands.

```shell
just containers system-image
just containers push-system-image
```

Then update `BASE_IMAGE_SHA256` in `MODULE.bazel`.

```shell
just containers nvidia-system-image
just containers push-nvidia-system-image
```

Then update `NVIDIA_BASE_IMAGE_SHA256` in `MODULE.bazel`.

```shell
just containers sysroot
just containers push-sysroot
```

Then update `SYSROOT_SHA256` in `bazel/extensions.bazel`.
