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

use alloc::{ffi::CString, vec::Vec};
use core::{mem::size_of, ops::Range, slice};

use oak_linux_boot_params::{BootE820Entry, BootParams, E820EntryType};
use x86_64::PhysAddr;
use zerocopy::{FromBytes, IntoBytes};

use crate::{
    BOOT_ALLOC, Measured,
    cmos::Cmos,
    fw_cfg::{FwCfg, find_suitable_dma_address},
};

/// Boot metadata for the Linux kernel.
///
/// This wraps one 4K page that contains the memory map and pointers to other
/// information needed for the kernel to boot (e.g. the command line, or SEV
/// metadata).
#[repr(transparent)]
#[derive(Debug)]
pub struct ZeroPage {
    inner: BootParams,
}

impl Default for ZeroPage {
    fn default() -> Self {
        Self::new()
    }
}

pub const BOOT_LOADER_TYPE_UNDEFINED: u8 = 0xFF;

impl ZeroPage {
    /// Constructs a empty zero page, filling in some magic values needed by the
    /// kernel.
    pub fn new() -> Self {
        let mut zero_page = BootParams::zeroed();
        // Magic constants.
        // See https://www.kernel.org/doc/html/latest/arch/x86/boot.html#the-real-mode-kernel-header for more details.
        zero_page.hdr.type_of_loader = BOOT_LOADER_TYPE_UNDEFINED; // loader type undefined
        zero_page.hdr.boot_flag = 0xAA55; // magic number
        zero_page.hdr.header = 0x53726448; // Magic "HdrS" string
        zero_page.hdr.kernel_alignment = 0x1000000; // Magic number from crosvm source.

        ZeroPage { inner: zero_page }
    }

    /// Fills the setup header fields with information from the kernel setup
    /// data if it is available on the fw_cfg device.
    ///
    /// The fw_cfg device will only provide this data when booting a compressed
    /// bzImage kernel, as it is split off from start of the bzImage file.
    ///
    /// See <https://www.kernel.org/doc/html/v6.3/x86/boot.html> for more information.
    ///
    /// Returns the measurement (SHA2-384 digest) of the setup data if it was
    /// found, otherwise the measurement is all zeros.
    pub fn try_fill_hdr_from_setup_data<P: crate::Platform>(
        &mut self,
        fw_cfg: &mut FwCfg<P>,
    ) -> Option<(Vec<u8>, [u8; 32])> {
        let file = fw_cfg.get_setup_file()?;
        let size = file.size();
        // We temporarily copy the setup data to the end of available mapped virtual
        // memory.
        let start = find_suitable_dma_address(size, self.inner.e820_table())
            .expect("no suitable DMA address available");
        let address = crate::phys_to_virt(start);

        // Safety: we have confirmed that the memory is backed by physical RAM and not
        // currently used for anything else. We will overwrite all of it, so
        // it does not have to be initialized.
        let buf = unsafe { slice::from_raw_parts_mut::<u8>(address.as_mut_ptr(), size) };
        let actual_size = fw_cfg.read_file(&file, buf).expect("could not read setup data");
        assert_eq!(actual_size, size, "setup data did not match expected size");
        // The initial ram disk location and size are not constant. We will overwrite it
        // later anyway, so we overwrite it with zeros before measuring so
        // we can get consistent measurement. See <https://www.kernel.org/doc/html/v6.7/arch/x86/boot.html> for
        // information on the  field offsets.
        *u32::mut_from_bytes(&mut buf[0x218..0x21C]).expect("invalid slice for initrd location") =
            0;
        *u32::mut_from_bytes(&mut buf[0x21C..0x220]).expect("invalid slice for initrd size") = 0;

        let measurement = buf.measure();

        // The header information starts at offset 0x01F1 from the start of the setup
        // data.
        let hdr_start = 0x1F1usize;
        // We can determine the end of the setup header information by adding the value
        // of the byte as offset 0x201 to the value 0x202.
        let hdr_end = 0x202usize + (buf[0x201] as usize);
        let src = &buf[hdr_start..hdr_end];
        // If we are loading an older kernel, the setup header might be a bit shorter.
        // New fields for more recent versions of the boot protocol are
        // added to the end of the setup header and there is padding after
        // header, so the resulting data stucture should still be understood
        // correctly by the kernel.
        let dest = &mut self.inner.hdr.as_mut_bytes()[..src.len()];
        dest.copy_from_slice(src);
        Some((buf.to_vec(), measurement))
    }

    /// Fills the E820 memory map (layout of the physical memory of the machine)
    /// in the zero page.
    ///
    /// We first try to read "etc/e820" via the QEMU fw_cfg interface, and if
    /// that is not available, fall back to querying RTC NVRAM.
    pub fn fill_e820_table<P: crate::Platform>(&mut self, fw_cfg: &mut FwCfg<P>) {
        // Try to load the E820 table from platform specific functions first
        let len_bytes = P::prefill_e820_table(&mut self.inner.e820_table).or_else(|_| unsafe {
            // Try to load the E820 table from fw_cfg.
            // Safety: BootE820Entry has the same structure as what qemu uses, and we're
            // limiting ourselves to up to 128 entries.
            log::debug!("Using fw_cfg to create the E820 table");
            fw_cfg.read_file_by_name(c"etc/e820", &mut self.inner.e820_table)
        });

        let e820_entries = match len_bytes {
            Ok(len_bytes) => {
                let e820_entries = len_bytes / size_of::<BootE820Entry>();
                self.inner.e820_table[..e820_entries].sort_unstable_by_key(|x| x.addr());
                e820_entries
            }
            Err(err) => {
                log::warn!("Failed to read 'etc/e820': {}, failing back to CMOS", err);

                // We don't support the early reservation entries, so panic if there are any.
                if fw_cfg.read_e820_reservation_table_size().unwrap_or(0) > 0 {
                    panic!("QEMU_E820_RESERVATION_TABLE was not empty!");
                }

                build_e820_from_nvram::<P>(&mut self.inner.e820_table)
                    .expect("failed to read from CMOS")
            }
        };

        self.inner.e820_entries = e820_entries as u8;
        self.validate_e820_table();

        // We leave a gap in the region [0xA0000,0xF0000) since historically this
        // contained hardware-related regions such as the VGA bios rom.
        self.ensure_e820_gap(0xA_0000, 0x5_0000);
        // Reserve [0xF0000,0x100000) as Stage0 initializes this memory to handle legacy
        // scans of the SMBIOS range.
        self.insert_e820_entry(BootE820Entry::new(0xF_0000, 0x1_0000, E820EntryType::RESERVED));

        for entry in self.inner.e820_table() {
            log::debug!(
                "early E820 entry: [{:#018x}-{:#018x}), len {}, type {}",
                entry.addr(),
                entry.addr() + entry.size(),
                entry.size(),
                entry.entry_type().unwrap()
            );
        }
    }

    /// Returns a reference to the E820 table inside the zero page.
    pub fn e820_table(&self) -> &[BootE820Entry] {
        self.inner.e820_table()
    }

    /// Inserts a new entry into the E820 table in the appropriate position
    /// (sorted by start address).
    ///
    /// If the new entry overlaps with one or more existing entries in the
    /// table, the effect depends on the entry type:
    ///
    /// - If the new entry has the same type as the existing entry the entries
    ///   will be merged into a single entry. Two adjacent entries of the same
    ///   type will also be merged.
    /// - If the new entry has a different type the new entry will be inserted
    ///   as is and the existing entry will be modified (trimmed or split into
    ///   two entries) to avoid the overlap.
    pub fn insert_e820_entry(&mut self, entry: BootE820Entry) {
        // Find the index where the entry must be inserted.
        let mut index = (0..(self.inner.e820_entries as usize))
            .find(|i| entry.addr() <= self.inner.e820_table[*i].addr())
            .unwrap_or(self.inner.e820_entries as usize);
        // Check whether the new entry overlaps with the previous entry.
        if index > 0 && self.inner.e820_table[index - 1].end() >= entry.addr() {
            let mut overlapping = self.inner.e820_table[index - 1];
            if overlapping.entry_type() == entry.entry_type() {
                // Merge the entry with the previous one.
                if overlapping.end() < entry.end() {
                    overlapping.set_size(entry.end() - overlapping.addr());
                    // Copy the modified overlapping entry back.
                    self.inner.e820_table[index - 1] = overlapping;
                }
                index -= 1;
            } else {
                if overlapping.end() > entry.end() {
                    // Split the overlapping range.
                    self.inner.insert_e820_entry(
                        BootE820Entry::new(
                            entry.end(),
                            overlapping.end() - entry.end(),
                            overlapping.entry_type().expect("invalid entry type"),
                        ),
                        index as u8,
                    );
                }

                // Trim the previous one to remove the overlap.
                overlapping.set_size(entry.addr() - overlapping.addr());
                self.inner.insert_e820_entry(entry, index as u8);
                // Copy the modified overlapping entry back.
                self.inner.e820_table[index - 1] = overlapping;
            }
        } else {
            self.inner.insert_e820_entry(entry, index as u8);
        }

        // Check whether the new entry overlaps with any existing later entries.
        let mut entry = self.inner.e820_table[index];
        let mut current = index + 1;
        while current < self.inner.e820_entries as usize
            && entry.end() >= self.inner.e820_table[current].addr()
        {
            if entry.end() >= self.inner.e820_table[current].end() {
                // The new entry completely covers the current one.
                self.inner.delete_e820_entry(current as u8);
            } else if entry.entry_type() == self.inner.e820_table[current].entry_type() {
                // Merge the entries.
                entry.set_size(self.inner.e820_table[current].end() - entry.addr());
                self.inner.delete_e820_entry(current as u8);
            } else {
                // Move and shrink the next entry.
                self.inner.e820_table[current]
                    .set_size(self.inner.e820_table[current].end() - entry.end());
                self.inner.e820_table[current].set_addr(entry.end());
                current += 1;
            }
        }

        // Copy the modified entry back.
        self.inner.e820_table[index] = entry;
    }

    /// Ensures that there are no E820 entries in a range.
    ///
    /// If the gap overlaps with one or more existing entries in the table, they
    /// will be either trimmed or deleted to ensure that there are no entries
    /// covering the gap.
    pub fn ensure_e820_gap(&mut self, start: usize, size: usize) {
        let end = start + size;
        while let Some(index) = (0..(self.inner.e820_entries as usize)).find(|i| {
            let entry = self.inner.e820_table[*i];
            end > entry.addr() && start < entry.end()
        }) {
            let mut entry = self.inner.e820_table[index];
            if entry.addr() < start && entry.end() > end {
                // The entry extends past the gap on both sides, split it.
                let new_entry = BootE820Entry::new(
                    end,
                    entry.end() - end,
                    entry.entry_type().expect("invalid entry type"),
                );
                entry.set_size(start - entry.addr());
                self.inner.e820_table[index] = entry;
                self.insert_e820_entry(new_entry)
            } else if entry.addr() >= start && entry.end() <= end {
                // The entry fits in the gap.
                self.inner.delete_e820_entry(index as u8);
            } else if entry.addr() < start {
                // The entry overlaps with the start of the gap.
                entry.set_size(start - entry.addr());
                self.inner.e820_table[index] = entry;
            } else {
                // The entry overlaps with the end of the gap.
                entry.set_size(entry.end() - end);
                entry.set_addr(end);
                self.inner.e820_table[index] = entry;
            }
        }
    }

    /// Checks if the given range is _not_ covered by any entries int he memory
    /// map.
    pub fn check_e820_gap(&self, range: Range<usize>) -> bool {
        !self
            .e820_table()
            .iter()
            .any(|&entry| entry.addr() < range.end && entry.end() > range.start)
    }

    fn validate_e820_table(&self) {
        // Check that the table is sorted.
        for i in 0..((self.inner.e820_entries - 1) as usize) {
            assert!(self.inner.e820_table[i].end() <= self.inner.e820_table[i + 1].addr());
        }
        // Check that all of the entry types are valid.
        assert_eq!(
            None,
            (0..(self.inner.e820_entries as usize))
                .find(|i| self.inner.e820_table[*i].entry_type().is_none())
        );
    }

    pub fn find_e820_entry(&self, addr: usize) -> Option<&BootE820Entry> {
        self.e820_table().iter().find(|&entry| entry.addr() <= addr && entry.end() > addr)
    }

    /// Updates the physical address of the ACPI RSDP table in the zero page.
    pub fn set_acpi_rsdp_addr(&mut self, addr: PhysAddr) {
        self.inner.acpi_rsdp_addr = addr.as_u64();
    }

    /// Updates the pointer to the command line parameter string in the zero
    /// page.
    pub fn set_cmdline<T: AsRef<str>>(&mut self, cmdline: T) {
        let cmdline =
            CString::new(cmdline.as_ref().as_bytes()).expect("invalid kernel command-line");
        let source = cmdline.as_bytes_with_nul();
        // Create and leak a buffer in the boot allocator so that it can outlive Stage
        // 0.
        let mut buf = Vec::with_capacity_in(source.len(), &BOOT_ALLOC);
        buf.resize(buf.capacity(), 0u8);
        buf.copy_from_slice(source);
        let buf = buf.leak();
        self.inner.hdr.cmd_line_ptr = buf.as_ptr() as u32;
        // As per the Linux boot protocol `cmdline_size` does not include the trailing
        // \0.
        self.inner.hdr.cmdline_size = cmdline.as_bytes().len() as u32;
    }

    /// Adds a header to the list of setup headers.
    ///
    /// `setup_data` needs to be mutable because underneath the covers it's a
    /// C-style linked list, and we need to assign the pointer to the next
    /// value in the list to the `next` field in its header.
    pub fn add_setup_data(&mut self, setup_data: &'static mut oak_linux_boot_params::CCSetupData) {
        // Put our header as the first element in the linked list.
        setup_data.header.next = self.inner.hdr.setup_data();
        self.inner.hdr.setup_data =
            &setup_data.header as *const oak_linux_boot_params::SetupData as u64;
    }

    /// Sets the address and size of the initial RAM disk.
    pub fn set_initial_ram_disk(&mut self, ram_disk: &'static [u8]) {
        // The address of the RAM disk will always be in the lower 32-bit range of
        // virtual memory since we only identity-map the first 1GiB of RAM and
        // QEMU only provides 32-bit addresses via the fw_cfg device.
        self.inner.hdr.ramdisk_image = ram_disk.as_ptr() as u64 as u32;
        // The size of the RAM disk will always fit into 32 bits since we only map a
        // maximum of 1GiB of RAM.
        self.inner.hdr.ramdisk_size = ram_disk.len() as u32;
    }

    /// Sets the type of loader for direct kernel boot
    pub fn set_type_of_loader(&mut self, loader_type: u8) {
        self.inner.hdr.type_of_loader = loader_type;
    }
}

/// Builds an E820 table by reading the low and high memory amount from CMOS.
///
/// The code is largely based on what SeaBIOS is doing (see `qemu_preinit()` and
/// `qemu_cfg_e820()` in <https://github.com/qemu/seabios/blob/b0d61ecef66eb05bd7a4eb7ada88ec5dab06dfee/src/fw/paravirt.c>),
/// but <https://wiki.osdev.org/Detecting_Memory_%28x86%29> is also a good read on the topic.
fn build_e820_from_nvram<P: crate::Platform>(
    e820_table: &mut [BootE820Entry],
) -> Result<usize, &'static str> {
    // Safety: (a) fw_cfg is available, so we're running under QEMU(ish) and (b)
    // there was no pre-built E820 table in fw_cfg; thus, we can reasonably
    // expect CMOS to available, as that's what SeaBIOS would use in that
    // situation to build the E820 table.
    let mut cmos = unsafe { Cmos::new::<P>() };
    let mut rs = cmos.low_ram_size()?;
    let high = cmos.high_ram_size()?;

    if rs <= 0x100000 {
        panic!("not enough RAM available: only {rs} bytes");
    }

    // Time to put all that we know together.
    // First, we'll leave the top 256K just below the 4G mark reserved for the BIOS
    // itself. Second, leave the last 4 pages of low memory as reserved just
    // below the BIOS area as reserved; according to SeaBIOS, KVM stores some
    // data structures there. Thus, the maximum memory we can have under 4G is
    // 0x1_0000_0000 - (44 * 0x1000) = 0xFFFB_C000.
    if rs > 0xFFFB_C000 {
        rs = 0xFFFB_C000;
    };
    let mut e820_entries = 2;
    e820_table[0] = BootE820Entry::new(0, rs as usize, E820EntryType::RAM);
    e820_table[1] =
        BootE820Entry::new(0xFFFB_C000, 0x1_0000_0000 - 0xFFFB_C000, E820EntryType::RESERVED);

    if high > 0 {
        e820_entries += 1;
        e820_table[2] = BootE820Entry::new(0x1_0000_0000, high as usize, E820EntryType::RAM);
    }

    Ok(e820_entries)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn insert_e820_entry_empty_table() {
        let expected = [BootE820Entry::new(0, 100, E820EntryType::RAM)];
        let mut zero_page = ZeroPage::new();

        zero_page.insert_e820_entry(BootE820Entry::new(0, 100, E820EntryType::RAM));

        assert_eq!(zero_page.e820_table(), &expected[..]);
    }

    #[test]
    pub fn insert_e820_entry_fill_gap() {
        let expected = [BootE820Entry::new(0, 100, E820EntryType::RAM)];
        let mut zero_page = ZeroPage::new();
        zero_page.inner.append_e820_entry(BootE820Entry::new(0, 40, E820EntryType::RAM));
        zero_page.inner.append_e820_entry(BootE820Entry::new(60, 40, E820EntryType::RAM));

        zero_page.insert_e820_entry(BootE820Entry::new(40, 20, E820EntryType::RAM));

        assert_eq!(zero_page.e820_table(), &expected[..]);
    }

    #[test]
    pub fn insert_e820_entry_fill_gap_overlapping() {
        let expected = [BootE820Entry::new(0, 100, E820EntryType::RAM)];
        let mut zero_page = ZeroPage::new();
        zero_page.inner.append_e820_entry(BootE820Entry::new(0, 40, E820EntryType::RAM));
        zero_page.inner.append_e820_entry(BootE820Entry::new(60, 40, E820EntryType::RAM));

        zero_page.insert_e820_entry(BootE820Entry::new(20, 60, E820EntryType::RAM));

        assert_eq!(zero_page.e820_table(), &expected[..]);
    }

    #[test]
    pub fn insert_e820_entry_split() {
        let expected = [
            BootE820Entry::new(0, 100, E820EntryType::RAM),
            BootE820Entry::new(100, 100, E820EntryType::RESERVED),
            BootE820Entry::new(200, 100, E820EntryType::RAM),
        ];
        let mut zero_page = ZeroPage::new();
        zero_page.inner.append_e820_entry(BootE820Entry::new(0, 300, E820EntryType::RAM));

        zero_page.insert_e820_entry(BootE820Entry::new(100, 100, E820EntryType::RESERVED));

        assert_eq!(zero_page.e820_table(), &expected[..]);
    }

    #[test]
    pub fn insert_e820_entry_disappear() {
        let expected = [BootE820Entry::new(0, 300, E820EntryType::RAM)];
        let mut zero_page = ZeroPage::new();
        zero_page.inner.append_e820_entry(BootE820Entry::new(0, 300, E820EntryType::RAM));

        zero_page.insert_e820_entry(BootE820Entry::new(100, 100, E820EntryType::RAM));

        assert_eq!(zero_page.e820_table(), &expected[..]);
    }

    #[test]
    pub fn insert_e820_entry_trim() {
        let expected = [
            BootE820Entry::new(0, 100, E820EntryType::RAM),
            BootE820Entry::new(100, 100, E820EntryType::RESERVED),
            BootE820Entry::new(200, 100, E820EntryType::RAM),
        ];
        let mut zero_page = ZeroPage::new();
        zero_page.inner.append_e820_entry(BootE820Entry::new(0, 150, E820EntryType::RAM));
        zero_page.inner.append_e820_entry(BootE820Entry::new(150, 150, E820EntryType::RAM));

        zero_page.insert_e820_entry(BootE820Entry::new(100, 100, E820EntryType::RESERVED));

        assert_eq!(zero_page.e820_table(), &expected[..]);
    }

    #[test]
    pub fn insert_e820_entry_cover() {
        let expected = [
            BootE820Entry::new(0, 100, E820EntryType::RAM),
            BootE820Entry::new(100, 100, E820EntryType::RESERVED),
            BootE820Entry::new(200, 100, E820EntryType::RAM),
        ];
        let mut zero_page = ZeroPage::new();
        zero_page.inner.append_e820_entry(BootE820Entry::new(0, 150, E820EntryType::RAM));
        zero_page.inner.append_e820_entry(BootE820Entry::new(150, 10, E820EntryType::RAM));
        zero_page.inner.append_e820_entry(BootE820Entry::new(160, 140, E820EntryType::RAM));

        zero_page.insert_e820_entry(BootE820Entry::new(100, 100, E820EntryType::RESERVED));

        assert_eq!(zero_page.e820_table(), &expected[..]);
    }

    #[test]
    pub fn gap_e820_no_op() {
        let expected = [
            BootE820Entry::new(0, 150, E820EntryType::RAM),
            BootE820Entry::new(160, 140, E820EntryType::RAM),
        ];
        let mut zero_page = ZeroPage::new();
        zero_page.inner.append_e820_entry(BootE820Entry::new(0, 150, E820EntryType::RAM));
        zero_page.inner.append_e820_entry(BootE820Entry::new(160, 140, E820EntryType::RAM));

        zero_page.ensure_e820_gap(150, 10);

        assert_eq!(zero_page.e820_table(), &expected[..]);
    }

    #[test]
    pub fn gap_e820_overlap_1() {
        let expected = [
            BootE820Entry::new(0, 100, E820EntryType::RAM),
            BootE820Entry::new(160, 140, E820EntryType::RAM),
        ];
        let mut zero_page = ZeroPage::new();
        zero_page.inner.append_e820_entry(BootE820Entry::new(0, 150, E820EntryType::RAM));
        zero_page.inner.append_e820_entry(BootE820Entry::new(160, 140, E820EntryType::RAM));

        zero_page.ensure_e820_gap(100, 55);

        assert_eq!(zero_page.e820_table(), &expected[..]);
    }

    #[test]
    pub fn gap_e820_overlap_2() {
        let expected = [
            BootE820Entry::new(0, 100, E820EntryType::RAM),
            BootE820Entry::new(180, 120, E820EntryType::RAM),
        ];
        let mut zero_page = ZeroPage::new();
        zero_page.inner.append_e820_entry(BootE820Entry::new(0, 150, E820EntryType::RAM));
        zero_page.inner.append_e820_entry(BootE820Entry::new(160, 140, E820EntryType::RAM));

        zero_page.ensure_e820_gap(100, 80);

        assert_eq!(zero_page.e820_table(), &expected[..]);
    }

    #[test]
    pub fn gap_e820_overlap_3() {
        let expected = [
            BootE820Entry::new(0, 100, E820EntryType::RAM),
            BootE820Entry::new(180, 120, E820EntryType::RAM),
        ];
        let mut zero_page = ZeroPage::new();
        zero_page.inner.append_e820_entry(BootE820Entry::new(0, 140, E820EntryType::RAM));
        zero_page.inner.append_e820_entry(BootE820Entry::new(150, 10, E820EntryType::RAM));
        zero_page.inner.append_e820_entry(BootE820Entry::new(170, 130, E820EntryType::RAM));

        zero_page.ensure_e820_gap(100, 80);

        assert_eq!(zero_page.e820_table(), &expected[..]);
    }

    #[test]
    pub fn gap_e820_cover_1() {
        let expected = [
            BootE820Entry::new(0, 140, E820EntryType::RAM),
            BootE820Entry::new(170, 130, E820EntryType::RAM),
        ];
        let mut zero_page = ZeroPage::new();
        zero_page.inner.append_e820_entry(BootE820Entry::new(0, 140, E820EntryType::RAM));
        zero_page.inner.append_e820_entry(BootE820Entry::new(150, 10, E820EntryType::RAM));
        zero_page.inner.append_e820_entry(BootE820Entry::new(170, 130, E820EntryType::RAM));

        zero_page.ensure_e820_gap(150, 10);

        assert_eq!(zero_page.e820_table(), &expected[..]);
    }

    #[test]
    pub fn gap_e820_split() {
        let expected = [
            BootE820Entry::new(0, 140, E820EntryType::RAM),
            BootE820Entry::new(170, 130, E820EntryType::RAM),
        ];
        let mut zero_page = ZeroPage::new();
        zero_page.inner.append_e820_entry(BootE820Entry::new(0, 300, E820EntryType::RAM));

        zero_page.ensure_e820_gap(140, 30);

        assert_eq!(zero_page.e820_table(), &expected[..]);
    }

    #[test]
    pub fn test_gap_exists() {
        let mut zero_page = ZeroPage::new();
        zero_page.inner.append_e820_entry(BootE820Entry::new(0, 1000, E820EntryType::RAM));
        zero_page.inner.append_e820_entry(BootE820Entry::new(2000, 4000, E820EntryType::RAM));

        assert!(!zero_page.check_e820_gap(0..1000));
        assert!(!zero_page.check_e820_gap(0..100));
        assert!(!zero_page.check_e820_gap(900..2100));
        assert!(!zero_page.check_e820_gap(900..1100));
        assert!(zero_page.check_e820_gap(1000..2000));
        assert!(zero_page.check_e820_gap(1100..1900));
        assert!(!zero_page.check_e820_gap(1100..2100));
        assert!(!zero_page.check_e820_gap(2000..2100));
        assert!(!zero_page.check_e820_gap(2000..4000));
        assert!(!zero_page.check_e820_gap(0..4000));
    }
}
