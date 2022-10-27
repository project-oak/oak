//
// Copyright © 2019 Intel Corporation
// SPDX-License-Identifier: Apache-2.0
//
// Copyright 2022 The Project Oak Authors
// SPDX-License-Identifier: Apache-2.0
//

#![no_std]

use x86_64::{PhysAddr, VirtAddr};

pub mod device;
pub mod mem;
pub mod pci;
pub mod virtio;

// TODO(#3394): Move to a shared crate.
pub trait InverseTranslator: Fn(PhysAddr) -> Option<VirtAddr> {}
impl<X: Fn(PhysAddr) -> Option<VirtAddr>> InverseTranslator for X {}
