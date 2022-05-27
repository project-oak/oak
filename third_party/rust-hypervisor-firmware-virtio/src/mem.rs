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

#[derive(Default)]
/// Provides a checked way to access memory offsets from a range of raw memory
pub struct MemoryRegion {
    base: u64,
    length: u64,
}

impl MemoryRegion {
    pub const fn new(base: u64, length: u64) -> MemoryRegion {
        MemoryRegion { base, length }
    }

    /// Take a slice and turn it into a region of memory
    pub fn from_bytes(data: &mut [u8]) -> MemoryRegion {
        MemoryRegion {
            base: data.as_ptr() as u64,
            length: data.len() as u64,
        }
    }

    // Expose the entire region as a byte slice
    pub fn as_bytes(&mut self) -> &mut [u8] {
        self.as_mut_slice(0, self.length)
    }

    /// Expose a section of the memory region as a slice
    pub fn as_mut_slice<T>(&mut self, offset: u64, length: u64) -> &mut [T] {
        assert!((offset + (length * core::mem::size_of::<T>() as u64)) <= self.length);
        unsafe { core::slice::from_raw_parts_mut((self.base + offset) as *mut T, length as usize) }
    }

    /// Read a value from a given offset
    fn read<T>(&self, offset: u64) -> T
    where
        T: Copy,
    {
        assert!((offset + (core::mem::size_of::<T>() - 1) as u64) < self.length);
        unsafe { *((self.base + offset) as *const T) }
    }

    /// Read a single byte at a given offset
    pub fn read_u8(&self, offset: u64) -> u8 {
        self.read(offset)
    }

    /// Read a single word at a given offset
    pub fn read_u16(&self, offset: u64) -> u16 {
        self.read(offset)
    }

    /// Read a single dword at a given offset
    pub fn read_u32(&self, offset: u64) -> u32 {
        self.read(offset)
    }

    // Read a single qword at a given offset
    pub fn read_u64(&self, offset: u64) -> u64 {
        self.read(offset)
    }

    /// Write a value at the given offset
    pub fn write<T>(&self, offset: u64, value: T) {
        assert!((offset + (core::mem::size_of::<T>() - 1) as u64) < self.length);
        unsafe {
            *((self.base + offset) as *mut T) = value;
        }
    }

    /// Write a single byte at given offset
    pub fn write_u8(&self, offset: u64, value: u8) {
        self.write(offset, value)
    }

    /// Write a single word at given offset
    pub fn write_u16(&self, offset: u64, value: u16) {
        self.write(offset, value)
    }

    /// Write a single dword at given offset
    pub fn write_u32(&self, offset: u64, value: u32) {
        self.write(offset, value)
    }

    /// Write a single qword at given offset
    pub fn write_u64(&self, offset: u64, value: u64) {
        assert!(offset + 7 < self.length);
        unsafe {
            *((self.base + offset) as *mut u64) = value;
        }
    }

    /// Read a value at given offset with a mechanism suitable for MMIO
    fn io_read<T>(&self, offset: u64) -> T {
        assert!((offset + (core::mem::size_of::<T>() - 1) as u64) < self.length);
        unsafe { core::ptr::read_volatile((self.base + offset) as *const T) }
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
            core::ptr::write_volatile((self.base + offset) as *mut T, value);
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
