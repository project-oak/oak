// Copyright © 2019 Intel Corporation
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

#![allow(dead_code)]

use x86_64::VirtAddr;

/// Provides a checked way to access memory offsets from a range of raw memory
pub struct MemoryRegion {
    base: VirtAddr,
    length: u64,
}

impl Default for MemoryRegion {
    fn default() -> Self {
        Self {
            base: VirtAddr::zero(),
            length: Default::default(),
        }
    }
}

impl MemoryRegion {
    pub const fn new(base: VirtAddr, length: u64) -> MemoryRegion {
        MemoryRegion { base, length }
    }

    /// Read a value at given offset with a mechanism suitable for MMIO
    fn io_read<T>(&self, offset: u64) -> T {
        assert!((offset + (core::mem::size_of::<T>() - 1) as u64) < self.length);
        unsafe { core::ptr::read_volatile((self.base + offset).as_ptr()) }
    }

    /// Read a single byte at given offset with a mechanism suitable for MMIO
    pub fn io_read_u8(&self, offset: u64) -> u8 {
        self.io_read(offset)
    }

    /// Read a single word at given offset with a mechanism suitable for MMIO
    pub fn io_read_u16(&self, offset: u64) -> u16 {
        self.io_read(offset)
    }

    /// Read a single dword at given offset with a mechanism suitable for MMIO
    pub fn io_read_u32(&self, offset: u64) -> u32 {
        self.io_read(offset)
    }

    /// Read a single qword at given offset with a mechanism suitable for MMIO
    pub fn io_read_u64(&self, offset: u64) -> u64 {
        self.io_read(offset)
    }

    /// Write a value at given offset using a mechanism suitable for MMIO
    fn io_write<T>(&self, offset: u64, value: T) {
        assert!((offset + (core::mem::size_of::<T>() - 1) as u64) < self.length);
        unsafe {
            core::ptr::write_volatile((self.base + offset).as_mut_ptr(), value);
        }
    }

    /// Write a single byte at given offset with a mechanism suitable for MMIO
    pub fn io_write_u8(&self, offset: u64, value: u8) {
        self.io_write(offset, value)
    }

    /// Write a single word at given offset with a mechanism suitable for MMIO
    pub fn io_write_u16(&self, offset: u64, value: u16) {
        self.io_write(offset, value)
    }

    /// Write a single dword at given offset with a mechanism suitable for MMIO
    pub fn io_write_u32(&self, offset: u64, value: u32) {
        self.io_write(offset, value)
    }

    /// Write a single qword at given offset with a mechanism suitable for MMIO
    pub fn io_write_u64(&self, offset: u64, value: u64) {
        self.io_write(offset, value)
    }
}
