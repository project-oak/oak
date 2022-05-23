use core::mem::size_of;

use crate::{
    boot::{E820Entry, Info},
    common,
};

// Structures from xen/include/public/arch-x86/hvm/start_info.h
#[derive(Debug)]
#[repr(C)]
pub struct StartInfo {
    magic: [u8; 4],
    version: u32,
    flags: u32,
    nr_modules: u32,
    modlist_paddr: u64,
    cmdline_paddr: u64,
    rsdp_paddr: u64,
    memmap_paddr: u64,
    memmap_entries: u32,
    _pad: u32,
}

#[derive(Clone, Copy, Debug)]
#[repr(C)]
struct MemMapEntry {
    addr: u64,
    size: u64,
    entry_type: u32,
    _pad: u32,
}

impl Info for StartInfo {
    fn name(&self) -> &str {
        "PVH Boot Protocol"
    }
    fn rsdp_addr(&self) -> u64 {
        self.rsdp_paddr
    }
    fn cmdline(&self) -> &[u8] {
        unsafe { common::from_cstring(self.cmdline_paddr) }
    }
    fn num_entries(&self) -> u8 {
        // memmap_paddr and memmap_entries only exist in version 1 or later
        if self.version < 1 || self.memmap_paddr == 0 {
            return 0;
        }
        self.memmap_entries as u8
    }
    fn entry(&self, idx: u8) -> E820Entry {
        assert!(idx < self.num_entries());
        let ptr = self.memmap_paddr as *const MemMapEntry;
        let entry = unsafe { *ptr.offset(idx as isize) };
        E820Entry {
            addr: entry.addr,
            size: entry.size,
            entry_type: entry.entry_type,
        }
    }
}

// The PVH Boot Protocol starts at the 32-bit entrypoint to our firmware.
extern "C" {
    fn ram32_start();
}

// The kind/name/desc of the PHV ELF Note are from xen/include/public/elfnote.h.
// This is the "Physical entry point into the kernel".
const XEN_ELFNOTE_PHYS32_ENTRY: u32 = 18;
type Name = [u8; 4];
type Desc = unsafe extern "C" fn();

// We make sure our ELF Note has an alignment of 4 for maximum compatibility.
// Some software (QEMU) calculates padding incorectly if alignment != 4.
#[repr(C, packed(4))]
pub struct Note {
    name_size: u32,
    desc_size: u32,
    kind: u32,
    name: Name,
    desc: Desc,
}

// This is: ELFNOTE(Xen, XEN_ELFNOTE_PHYS32_ENTRY, .quad ram32_start)
#[link_section = ".note"]
#[used]
pub static PVH_NOTE: Note = Note {
    name_size: size_of::<Name>() as u32,
    desc_size: size_of::<Desc>() as u32,
    kind: XEN_ELFNOTE_PHYS32_ENTRY,
    name: *b"Xen\0",
    desc: ram32_start,
};
