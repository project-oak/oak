# Kernel Measurement Prediction Tool

When booting a VM the kernel and its associated setup data is measured by the
Stage 0 firmware. The VMM accepts a single bzImage format kernel file. It then
splits it into two parts, the kernel image and the kernel setup data. The VMM
also makes modifications to the setup data before passing it to Stage 0 via the
fw_cfg device.

Stage 0 measures these split, modified components rather than the original
bzImage kernel. This tool can be used to predict the Stage 0 measurements of
these components from a bzImage kernel.

The tool can be run on the command line, for example:

```bash
just oak_containers_kernel_subjects
```

See the justfile for details on the command structure.

The tool can also be run using a bazel rule. See
[oak_restricted_kernel_wrapper/rules.bzl] for an example.
