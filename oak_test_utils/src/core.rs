//
// Copyright 2026 The Project Oak Authors
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

//! Utilities for parsing and searching guest-physical memory from ELF core
//! dumps.

use std::ops::Range;

use goblin::elf::{Elf, ProgramHeader, program_header::PT_LOAD};

/// A parsed QEMU guest-memory ELF core dump, providing access to the guest's
/// physical memory.
pub struct Core {
    /// Raw bytes of the ELF core dump file.
    pub raw: Box<[u8]>,
    /// Program headers parsed from `raw`, describing the guest-memory mappings.
    pub program_headers: Vec<ProgramHeader>,
}

impl Core {
    /// Parses the raw bytes of a QEMU guest-memory ELF core dump.
    pub fn parse(raw: Box<[u8]>) -> anyhow::Result<Self> {
        let program_headers = Elf::parse(&raw)
            .map_err(|e| anyhow::anyhow!("parsing ELF core dump: {e}"))?
            .program_headers;
        Ok(Self { raw, program_headers })
    }

    /// Iterates over the segments that map bytes from guest memory.
    pub fn load_segments(&self) -> impl Iterator<Item = &ProgramHeader> + '_ {
        self.program_headers.iter().filter(|h| h.p_type == PT_LOAD && h.p_filesz > 0)
    }

    /// Returns the guest-physical address (GPA) at which `needle` occurs within
    /// guest memory.
    pub fn find_in_guest_memory(&self, needle: &[u8]) -> Vec<u64> {
        assert!(!needle.is_empty(), "needle must not be empty");
        let mut hits = Vec::new();
        for header in self.load_segments() {
            let mut range = header.file_range();
            range.end = range.end.min(self.raw.len());
            if range.start >= range.end {
                continue;
            }
            // The segment's first file byte maps to guest-physical address
            // `p_paddr`, so an offset within `haystack` is that same offset past
            // `p_paddr`.
            let haystack = &self.raw[range];
            for (offset, window) in haystack.windows(needle.len()).enumerate() {
                if window == needle {
                    hits.push(header.p_paddr + offset as u64);
                }
            }
        }
        hits
    }

    /// Reads the bytes of guest-physical memory in the address range `range`,
    /// returning `None` if the range is empty or not fully contained in a
    /// single mapped segment.
    pub fn read_guest_memory(&self, range: Range<u64>) -> Option<&[u8]> {
        if range.is_empty() {
            return None;
        }
        for header in self.load_segments() {
            let seg_start = header.p_paddr;
            let seg_end = seg_start + header.p_filesz;
            if range.start < seg_start || range.end > seg_end {
                continue;
            }
            let seg_range = header.file_range();
            let file_start = seg_range.start + (range.start - seg_start) as usize;
            let file_end = file_start + (range.end - range.start) as usize;
            if file_end <= self.raw.len() {
                return Some(&self.raw[file_start..file_end]);
            }
        }
        None
    }

    /// Reads a fixed-size `N`-byte array of guest-physical memory starting at
    /// `phys_addr`, returning `None` if the range is not fully mapped.
    pub fn read_fixed<const N: usize>(&self, phys_addr: u64) -> Option<[u8; N]> {
        let bytes = self.read_guest_memory(phys_addr..phys_addr + N as u64)?;
        Some(bytes.try_into().expect("read_guest_memory returns exactly N bytes"))
    }
}
