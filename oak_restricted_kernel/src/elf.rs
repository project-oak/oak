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

use goblin::elf64::program_header::ProgramHeader;
use x86_64::VirtAddr;

/// Interpret raw memory at the given address as an ELF header and return the
/// program headers.
///
/// Safety: this virtual address must be valid and contain ELF headers and
/// program headers.
pub unsafe fn get_phdrs(addr: VirtAddr) -> &'static [ProgramHeader] {
    let raw_header = unsafe {
        core::slice::from_raw_parts(
            addr.as_u64() as *const u8,
            goblin::elf::header::header64::SIZEOF_EHDR,
        )
    };
    let header = goblin::elf::Elf::parse_header(raw_header).unwrap();
    unsafe {
        ProgramHeader::from_raw_parts(
            (addr.as_u64() + header.e_phoff) as *const ProgramHeader,
            header.e_phnum as usize,
        )
    }
}
