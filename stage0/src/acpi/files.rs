//
// Copyright 2025 The Project Oak Authors
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

use alloc::{alloc::Global, boxed::Box, collections::BTreeMap, ffi::CString};
use core::{
    alloc::{Allocator, Layout},
    borrow::{Borrow, BorrowMut},
    ffi::CStr,
    ops::{Deref, DerefMut},
};

use super::Zone;

/// A really simple virtual file system interface to store chunks of bytes by
/// name, and access said chunks later by the name.
pub trait Files {
    /// Allocate a new file.
    ///
    /// This is similar to the normal `Allocator` API, but we may need to treat
    /// files in different `zone`-s differently (e.g. allocate from different
    /// pools of memory), so we can't just piggyback on the `Allocator` trait
    /// directly.
    ///
    /// Alignment guarantees requested the layout are implementation-specific
    /// (for example, if you use a non-static buffer of u8-s as the backing
    /// store, we can't guarantee alignment as the data can be moved around
    /// freely after allocation.)
    ///
    /// Returns an error if the file already exists.
    fn allocate(
        &mut self,
        name: &CStr,
        layout: Layout,
        zone: Zone,
    ) -> Result<&mut [u8], &'static str>;

    /// Get a mutable reference to file contents, if such file exists.
    fn get_file_mut(&mut self, name: &CStr) -> Result<&mut [u8], &'static str>;

    /// Access the contents of the named file, if it exists.
    fn get_file(&self, name: &CStr) -> Result<&[u8], &'static str>;

    /// Returns the first file with a name that matches the suffix, if it
    /// exists.
    fn find_file_suffix(&self, suffix: &CStr) -> Option<&[u8]>;
}

/// Wrapper for a file, as they may come from different zones.
pub enum File<'a, 'b, L: Allocator, H: Allocator> {
    /// A file in `Zone::FSeg` (stored in the EBDA, e.g. the RSDP)
    Low(Box<[u8], &'a L>),

    /// A file in `Zone::High` (stored somewhwere else in memory)
    High(Box<[u8], &'b H>),

    #[cfg(test)]
    /// Testing only: an arbitrary pointer. This is useful for cases when we
    /// want to predictable addresses and not be at the whim of the allocator.
    /// As writing or reading from arbitrary pointers is unsafe, you'll only
    /// be able to get zero-length slices as the backing store for this type
    /// of file.
    Fake(core::ptr::NonNull<u8>),
}

impl<L: Allocator, H: Allocator> File<'_, '_, L, H> {
    /// Leaks the memory owned by this file, if any.
    pub fn leak(self) {
        match self {
            Self::Low(file) => {
                Box::leak(file);
            }
            Self::High(file) => {
                Box::leak(file);
            }
            #[cfg(test)]
            Self::Fake(_) => {}
        };
    }
}

impl<L: Allocator, H: Allocator> Deref for File<'_, '_, L, H> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        match self {
            Self::Low(file) => file,
            Self::High(file) => file,
            #[cfg(test)]
            Self::Fake(data) => {
                // Safety: any non-null pointer can be turned into a zero-length slice, as you
                // can't read from or write to the resulting slice.
                unsafe { core::slice::from_raw_parts(data.as_ref(), 0) }
            }
        }
    }
}

impl<L: Allocator, H: Allocator> DerefMut for File<'_, '_, L, H> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            Self::Low(file) => file.borrow_mut(),
            Self::High(file) => file.borrow_mut(),
            #[cfg(test)]
            Self::Fake(data) => {
                // Safety: any non-null pointer can be turned into a zero-length slice, as you
                // can't read from or write to the resulting slice.
                unsafe { core::slice::from_raw_parts_mut(data.as_mut(), 0) }
            }
        }
    }
}

/// Storage for files loaded by table_loader.
///
/// As files can be in two zones (`Zone::FSeg` and `Zone::High`) we take two
/// allocators as parameters where the files will be allocated from,
/// respectively.
pub struct MemFiles<L: Allocator + 'static, H: Allocator + 'static> {
    low_allocator: &'static L,
    high_allocator: &'static H,
    files: BTreeMap<CString, File<'static, 'static, L, H>>,
}

impl<L: Allocator + 'static, H: Allocator + 'static> MemFiles<L, H> {
    pub const fn new(low_allocator: &'static L, high_allocator: &'static H) -> Self {
        Self { low_allocator, high_allocator, files: BTreeMap::new() }
    }

    /// Leaks all the files in this storage.
    ///
    /// As MemFiles is just glorified bag of `Box`-es, this just calls
    /// `Box::leak` on all of them.
    pub fn leak(self) {
        for file in self.files.into_values() {
            file.leak();
        }
    }

    #[cfg(test)]
    /// Testing only: store some contents in FSeg, and panic if allocation
    /// fails.
    pub fn new_file(&mut self, name: &CStr, contents: &[u8]) {
        let new_file = self
            .allocate(name, Layout::from_size_align(contents.len(), 1).unwrap(), Zone::FSeg)
            .unwrap();
        new_file.copy_from_slice(contents);
    }

    #[cfg(test)]
    /// Testing only: store a fake entry.
    pub fn new_file_ptr(
        &mut self,
        name: &CStr,
        ptr: core::ptr::NonNull<u8>,
    ) -> core::result::Result<(), &'static str> {
        if self.files.contains_key(name) {
            return Err("file already exists");
        }
        self.files.insert(name.into(), File::Fake(ptr));
        Ok(())
    }
}

/// By default you get a MemFiles that just uses the global allocator.
impl Default for MemFiles<Global, Global> {
    fn default() -> Self {
        Self::new(&Global, &Global)
    }
}

impl<L: Allocator + 'static, H: Allocator + 'static> Files for MemFiles<L, H> {
    fn allocate(
        &mut self,
        name: &CStr,
        layout: Layout,
        zone: Zone,
    ) -> Result<&mut [u8], &'static str> {
        if self.files.contains_key(name) {
            return Err("file already exists");
        }

        // These branches look similar, but each step is different because the different
        // allocator used.
        let file = match zone {
            Zone::High => {
                let mut mem = self
                    .high_allocator
                    .allocate_zeroed(layout)
                    .map_err(|_| "failed to allocate memory for file")?;
                // Safety: the pointer is not null (guaranteed by `NonNull`); the contents are
                // zeroed and any alignment is valid for `u8`; there are no aliases to the
                // memory location; we use the correct allocator for the `Box`.
                let boxed = unsafe { Box::from_raw_in(mem.as_mut(), self.high_allocator) };
                File::High(boxed)
            }
            Zone::FSeg => {
                let mut mem = self
                    .low_allocator
                    .allocate_zeroed(layout)
                    .map_err(|_| "failed to allocate memory for file")?;
                // Safety: the pointer is not null (guaranteed by `NonNull`); the contents are
                // zeroed and any alignment is valid for `u8`; there are no aliases to the
                // memory location; we use the correct allocator for the `Box`.
                let boxed = unsafe { Box::from_raw_in(mem.as_mut(), self.low_allocator) };
                File::Low(boxed)
            }
        };

        // Sanity check: make sure that the memory in the box is indeed correctly
        // aligned.
        assert!(file.as_ptr().align_offset(layout.align()) == 0);

        self.files.insert(name.into(), file);
        self.get_file_mut(name)
    }

    fn get_file_mut(&mut self, name: &CStr) -> Result<&mut [u8], &'static str> {
        let file = self.files.get_mut(name).ok_or("file not found")?;
        Ok(file.borrow_mut())
    }

    fn get_file(&self, name: &CStr) -> Result<&[u8], &'static str> {
        let file = self.files.get(name).ok_or("file not found")?;
        Ok(file.borrow())
    }

    fn find_file_suffix(&self, suffix: &CStr) -> Option<&[u8]> {
        for (name, contents) in self.files.iter() {
            if !name.as_bytes().ends_with(suffix.to_bytes()) {
                continue;
            }
            return Some(contents.borrow());
        }
        None
    }
}
