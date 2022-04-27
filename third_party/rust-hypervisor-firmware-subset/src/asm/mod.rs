// Derived from Cloud Hypervisor, https://github.com/cloud-hypervisor/rust-hypervisor-firmware/

use core::arch::global_asm;

global_asm!(include_str!("ram32.s"), options(att_syntax, raw));
