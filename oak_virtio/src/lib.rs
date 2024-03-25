//
// Copyright 2022 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

//! Simple virtio drivers implemented based on polling.
//!
//! This crate assumes that an identity mapping is used in page tables, so that
//! guest-virtual and guest-physical addresses are the same.

#![no_std]
#![feature(allocator_api)]
#![feature(let_chains)]

use x86_64::{PhysAddr, VirtAddr};

extern crate alloc;
#[cfg(test)]
extern crate std;

pub mod console;
pub mod queue;
#[cfg(test)]
mod test;
pub mod vsock;

/// Read bytes from a source.
///
/// This trait is similar to the <std::io::Read> trait, except that this trait
/// is pared down to a minimum and works in a `no_std` environment.
pub trait Read {
    /// Read bytes until `data` has been filled.
    fn read_exact(&mut self, data: &mut [u8]) -> anyhow::Result<()>;
}

/// Write bytes to a source.
///
/// This trait is similar to the <std::io::Write> trait, except that this trait
/// is pared down to a minimum and works in a `no_std` environment.
pub trait Write {
    /// Write all bytes in `data`.
    fn write_all(&mut self, data: &[u8]) -> anyhow::Result<()>;

    /// Flush any output buffers, if they exist.
    fn flush(&mut self) -> anyhow::Result<()>;
}

/// The vendor ID for virtio PCI devices.
const PCI_VENDOR_ID: u16 = 0x1AF4;

/// Memory address translation functions.
pub trait Translator: Fn(VirtAddr) -> Option<PhysAddr> {}
impl<X: Fn(VirtAddr) -> Option<PhysAddr>> Translator for X {}
pub trait InverseTranslator: Fn(PhysAddr) -> Option<VirtAddr> {}
impl<X: Fn(PhysAddr) -> Option<VirtAddr>> InverseTranslator for X {}
