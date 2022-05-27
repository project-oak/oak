This crate contains code extracted from the Rust Hypervisor Firmware code base:
https://github.com/cloud-hypervisor/rust-hypervisor-firmware

Rust Hypervisor Firmware is, as the name suggests, designed to be firmware for
virtual machines that is able to load other kernels. The code here is the subset
of Rust Hypervisor Firmware code that's necessary to bootstrap something on bare
metal, as we're interested in just getting the machine going (without relying on
disk images) and intend to build the kernel directly on top.
