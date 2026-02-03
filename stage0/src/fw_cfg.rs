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

// TODO(#3703): Remove when fixed.
#![allow(clippy::extra_unused_type_parameters)]

use alloc::{vec, vec::Vec};
use core::{cmp::min, ffi::CStr};

use bitflags::bitflags;
use oak_linux_boot_params::{BootE820Entry, E820EntryType};
use oak_sev_guest::io::{IoPortFactory, PortReader, PortWriter};
use x86_64::{
    PhysAddr, VirtAddr,
    structures::paging::{PageSize, Size4KiB},
};
use zerocopy::{FromBytes, IntoBytes};

use crate::{BootAllocator, allocator::Shared, hal::Port};

// See https://www.qemu.org/docs/master/specs/fw_cfg.html for documentation about the various data structures and constants.
const FWCFG_PORT_SELECTOR: u16 = 0x510;
const FWCFG_PORT_DATA: u16 = 0x511;
const FWCFG_PORT_DMA: u16 = 0x514;

const SIGNATURE: &[u8] = b"QEMU";

bitflags! {
    /// The interface features supported by the device.
    struct Features: u8 {
        /// Indicates that the device supports the traditional byte-by-byte interface.
        const TRADITIONAL = 1 << 0;
        /// Indicates that the device supports the DMA interface.
        const DMA = 1 << 1;
    }
}

/// A single 4KiB buffer that is 4KiB page-aligned.
#[repr(C, align(4096))]
#[derive(Debug)]
pub struct DmaBuffer {
    data: [u8; Size4KiB::SIZE as usize],
}

static_assertions::assert_eq_size!(DmaBuffer, [u8; Size4KiB::SIZE as usize]);

impl Default for DmaBuffer {
    fn default() -> Self {
        DmaBuffer { data: [0u8; Size4KiB::SIZE as usize] }
    }
}

/// Selector keys for "well-known" fw_cfg entries.
///
/// See QEMU include/standard-headers/linux/qemu_fw_cfg.h for the authoritative
/// list.
#[allow(dead_code)]
#[repr(u16)]
enum FwCfgItems {
    Signature = 0x0000,
    Features = 0x0001,
    KernelAddr = 0x0007,
    KernelSize = 0x0008,
    InitrdAddr = 0x000a,
    InitrdSize = 0x000b,
    KernelEntry = 0x0010,
    KernelData = 0x0011,
    InitrdData = 0x0012,
    CmdlineAddr = 0x0013,
    CmdlineSize = 0x0014,
    CmdlineData = 0x0015,
    SetupAddr = 0x0016,
    SetupSize = 0x0017,
    SetupData = 0x0018,
    FileDir = 0x0019,
    E820ReservationTable = 0x8003,
}

/// an individual file entry, 64 bytes total
#[repr(C)]
#[derive(IntoBytes, FromBytes)]
pub struct DirEntry {
    /// size of referenced fw_cfg item, big-endian
    size: u32,
    /// selector key of fw_cfg item, big-endian
    select: u16,
    _reserved: u16,
    /// fw_cfg item name, NUL-terminated ascii
    name: [u8; 56],
}
static_assertions::assert_eq_size!(DirEntry, [u8; 64usize]);

impl Default for DirEntry {
    fn default() -> Self {
        Self { size: 0, select: 0, _reserved: 0, name: [0; 56] }
    }
}

impl DirEntry {
    #[cfg(test)]
    pub fn new(name: &CStr, size: u32, selector: u16) -> Self {
        let mut entry_name = [0u8; 56];
        entry_name[..name.to_bytes_with_nul().len()].copy_from_slice(name.to_bytes_with_nul());
        DirEntry { size: size.to_be(), select: selector, _reserved: 0, name: entry_name }
    }

    fn new_for_selector(size: u32, selector: FwCfgItems) -> Self {
        Self { size: size.to_be(), select: (selector as u16).to_be(), ..Default::default() }
    }

    pub fn name(&self) -> &CStr {
        CStr::from_bytes_until_nul(&self.name).unwrap()
    }

    pub fn size(&self) -> usize {
        u32::from_be(self.size) as usize
    }

    pub fn selector(&self) -> u16 {
        u16::from_be(self.select)
    }
}

impl core::fmt::Debug for DirEntry {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("DirEntry")
            .field("name", &self.name())
            .field("size", &self.size())
            .field("select", &self.selector())
            .finish()
    }
}

/// Wrapper for the QEMU Firmware Configuration device.
///
/// See <https://www.qemu.org/docs/master/specs/fw_cfg.html> for more details.
pub struct FwCfg<P: crate::Platform> {
    selector: Port<u16>,
    data: Port<u8>,
    dma_high: Port<u32>,
    dma_low: Port<u32>,
    dma_buf: Shared<DmaBuffer, &'static BootAllocator, P>,
    dma_access: Shared<FwCfgDmaAccess, &'static BootAllocator, P>,
    dma_enabled: bool,
}

impl<P: crate::Platform> FwCfg<P> {
    /// # Safety
    ///
    /// While we do probe for the existence of the QEMU fw_cfg device, reading
    /// or writing to I/O ports that are not in use is inherently undefined
    /// behaviour. What's worse, if there happens to be some other device
    /// using those I/O ports, the results are completely unknowable.
    ///
    /// The caller has to guarantee that at least doing the probe will not cause
    /// any adverse effects.
    pub unsafe fn new(alloc: &'static BootAllocator) -> Result<Self, &'static str> {
        let port_factory = P::port_factory();
        let mut fwcfg = Self {
            selector: port_factory.new_writer(FWCFG_PORT_SELECTOR),
            data: port_factory.new_reader(FWCFG_PORT_DATA),
            dma_high: port_factory.new_writer(FWCFG_PORT_DMA),
            // The DMA address must be big-endian encoded, so the low address is 4 bytes further
            // than the high address.
            dma_low: port_factory.new_writer(FWCFG_PORT_DMA + 4),
            dma_buf: Shared::new_in(DmaBuffer::default(), alloc),
            dma_access: Shared::new_in(FwCfgDmaAccess::default(), alloc),
            dma_enabled: false,
        };

        // Make sure the fw_cfg device is available. If the device is not available,
        // writing and reading to I/O ports is undefined behaviour.
        fwcfg.write_selector(FwCfgItems::Signature as u16)?;
        let mut signature = [0u8; SIGNATURE.len()];
        fwcfg.read(&mut signature)?;

        // Check whether DMA is enabled.
        let mut features = 0u8;
        fwcfg.write_selector(FwCfgItems::Features as u16)?;
        fwcfg.read(&mut features)?;

        let features =
            Features::from_bits(features).ok_or("invalid fw_cfg device features received")?;
        if features.contains(Features::DMA) {
            fwcfg.dma_enabled = true;
        }

        if signature == SIGNATURE { Ok(fwcfg) } else { Err("QEMU fw_cfg device not available") }
    }

    /// Returns an iterator over the files in the fw_cfg system.
    ///
    /// # Safety
    ///
    /// You should consume the iterator fully before calling any other methods
    /// of this struct, or at the very least don't use the iterator after
    /// calling some other function. (This means that, for example, you
    /// shouldn't try to read the files while iterating over the
    /// directory contents.)
    /// If you call any other methods, the iterator will be in an undefined
    /// state and unsafe to read from.
    pub unsafe fn dir(&mut self) -> impl Iterator<Item = DirEntry> + '_ {
        self.write_selector(FwCfgItems::FileDir as u16).unwrap();

        // We don't represent FwCfgFiles as a struct, as you can't do that in safe Rust.
        // Therefore, read fields individually.
        let count = {
            let mut buf = [0u8; 4];
            self.read(&mut buf).unwrap();
            u32::from_be_bytes(buf)
        };

        (0..count).map(|_| {
            let mut file = DirEntry::default();
            self.read(&mut file).unwrap();
            file
        })
    }

    pub fn find(&mut self, name: &CStr) -> Option<DirEntry> {
        // Safety: this is safe as we don't leak the iterator.
        unsafe { self.dir() }.find(|file| file.name() == name)
    }

    /// Reads the contents of a file to a predetermined struct.
    /// Returns the number of bytes read.
    ///
    /// # Safety
    ///
    /// While we will never write beyond the memory allocated to `object`, it is
    /// up to the caller to ensure that the type of `object` is a faithful
    /// representation of the contents of the file; otherwise, `object` may
    /// be left in an invalid state.
    pub unsafe fn read_file_by_name<T: IntoBytes + FromBytes>(
        &mut self,
        name: &CStr,
        object: &mut T,
    ) -> Result<usize, &'static str> {
        let entry = self.find(name);
        if let Some(file) = entry {
            self.read_file(&file, object.as_mut_bytes())
        } else {
            Err("couldn't find requested file")
        }
    }

    /// Reads the size of the E820 reservation table.
    ///
    /// This table predates the file interface and thus has its own selector.
    pub fn read_e820_reservation_table_size(&mut self) -> Result<u32, &'static str> {
        let mut reservation_count: u32 = 0;
        self.write_selector(FwCfgItems::E820ReservationTable as u16)?;
        self.read(&mut reservation_count)?;
        Ok(reservation_count)
    }

    /// Reads contents of a file; returns the number of bytes actually read.
    ///
    /// If reading files via DMA is supported, it will use DMA. If not it will
    /// fall back to reading byte by byte.
    ///
    /// The buffer `buf` will be filled to capacity if the file is larger;
    /// if it is shorter, the trailing bytes will not be touched.
    pub fn read_file(&mut self, file: &DirEntry, buf: &mut [u8]) -> Result<usize, &'static str> {
        self.write_selector(file.selector())?;
        let len = min(buf.len(), file.size());
        if self.dma_enabled {
            self.read_buf_dma(&mut buf[..len])?;
        } else {
            self.read_buf(&mut buf[..len])?;
        }
        Ok(len)
    }

    /// Reads contents of a file; returns a vector with the bytes read.
    ///
    /// See <read_file> for more information.
    pub fn read_file_vec(&mut self, file: &DirEntry) -> Result<Vec<u8>, &'static str> {
        self.write_selector(file.selector())?;
        let mut buf = vec![0; file.size()];

        if self.dma_enabled {
            self.read_buf_dma(&mut buf)?;
        } else {
            self.read_buf(&mut buf)?;
        }

        Ok(buf)
    }

    /// Reads the size of the kernel command-line.
    pub fn read_cmdline_size(&mut self) -> Result<u32, &'static str> {
        let mut cmdline_size: u32 = 0;
        self.write_selector(FwCfgItems::CmdlineSize as u16)?;
        self.read(&mut cmdline_size)?;
        Ok(cmdline_size)
    }

    /// Gets an unnamed file representation of the kernel command-line using the
    /// dedicated selector.
    ///
    /// Returns `None` if the kernel command-line size is 0.
    pub fn get_cmdline_file(&mut self) -> Option<DirEntry> {
        let size = self.read_cmdline_size().expect("couldn't read cmdline size");
        if size == 0 {
            None
        } else {
            Some(DirEntry::new_for_selector(size, FwCfgItems::CmdlineData))
        }
    }

    /// Reads the size of the initial RAM disk.
    pub fn read_initrd_size(&mut self) -> Result<u32, &'static str> {
        let mut initrd_size: u32 = 0;
        self.write_selector(FwCfgItems::InitrdSize as u16)?;
        self.read(&mut initrd_size)?;
        Ok(initrd_size)
    }

    /// Gets an unnamed file representation of the initial RAM disk using the
    /// dedicated selector.
    ///
    /// Returns `None` if the initial RAM disk size is 0.
    pub fn get_initrd_file(&mut self) -> Option<DirEntry> {
        let size = self.read_initrd_size().expect("couldn't read initrd size");
        if size == 0 {
            None
        } else {
            Some(DirEntry::new_for_selector(size, FwCfgItems::InitrdData))
        }
    }

    /// Reads the size of the kernel.
    pub fn read_kernel_size(&mut self) -> Result<u32, &'static str> {
        let mut kernel_size: u32 = 0;
        self.write_selector(FwCfgItems::KernelSize as u16)?;
        self.read(&mut kernel_size)?;
        Ok(kernel_size)
    }

    /// Gets an unnamed file representation of the kernel using the dedicated
    /// selector.
    ///
    /// Returns `None` if the kernel size is 0.
    pub fn get_kernel_file(&mut self) -> Option<DirEntry> {
        let size = self.read_kernel_size().expect("couldn't read kernel size");
        if size == 0 {
            None
        } else {
            Some(DirEntry::new_for_selector(size, FwCfgItems::KernelData))
        }
    }

    /// Reads the size of the setup information for the kernel.
    pub fn read_setup_size(&mut self) -> Result<u32, &'static str> {
        let mut setup_size: u32 = 0;
        self.write_selector(FwCfgItems::SetupSize as u16)?;
        self.read(&mut setup_size)?;
        Ok(setup_size)
    }

    /// Gets an unnamed file representation of the kernel's setup information
    /// using the dedicated selector.
    ///
    /// Returns `None` if the kernel size is 0.
    pub fn get_setup_file(&mut self) -> Option<DirEntry> {
        let size = self.read_setup_size().expect("couldn't read setup size");
        if size == 0 { None } else { Some(DirEntry::new_for_selector(size, FwCfgItems::SetupData)) }
    }

    fn write_selector(&mut self, selector: u16) -> Result<(), &'static str> {
        // Safety: we make sure the device is available when initializing FwCfg.
        unsafe { self.selector.try_write(selector) }
    }

    fn read<T: IntoBytes + FromBytes>(&mut self, object: &mut T) -> Result<(), &'static str> {
        self.read_buf(object.as_mut_bytes())
    }

    fn read_buf(&mut self, buf: &mut [u8]) -> Result<(), &'static str> {
        for i in buf {
            // Safety: We make sure that the device is available in `new()`, so reading from
            // the port is safe.
            *i = unsafe { self.data.try_read() }?;
        }
        Ok(())
    }

    fn read_buf_dma(&mut self, buf: &mut [u8]) -> Result<(), &'static str> {
        let mut chunks_mut = buf.chunks_mut(Size4KiB::SIZE as usize);
        for chunk in chunks_mut.by_ref() {
            self.read_chunk_dma(chunk)?;
        }

        Ok(())
    }

    fn read_chunk_dma(&mut self, chunk: &mut [u8]) -> Result<(), &'static str> {
        if chunk.len() > self.dma_buf.data[..].len() {
            return Err("chunk is larger than the DMA buffer");
        }

        // We always use an identity mapping. We use the shared DMA buffer as a
        // bounce-buffer to account for potential memory encryption.
        let address = PhysAddr::new(self.dma_buf.data.as_ptr() as usize as u64);
        // The length of the buffer will always fit in 32 bits, since we only map the
        // first 1GiB of physical memory to virtual memory.
        let length = chunk.len() as u32;
        *self.dma_access = FwCfgDmaAccess::new(ControlFlags::READ, length, address);
        let dma_access_address = self.dma_access.as_ref() as *const _ as usize as u64;
        let dma_low = (dma_access_address & 0xFFFFFFFF) as u32;
        let dma_high = (dma_access_address >> 32) as u32;
        // The DMA address halves must be written in big endian format, and the high
        // half must be written before the low half.
        // Safety: We make sure that the device is available in `new()`, so writing to
        // the ports is safe.
        unsafe {
            self.dma_high.try_write(dma_high.to_be())?;
            self.dma_low.try_write(dma_low.to_be())?;
        }

        // Memory fence to make sure that the DMA operation is complete before we read
        // the result.
        core::sync::atomic::fence(core::sync::atomic::Ordering::SeqCst);

        // The control field will be cleared if the DMA operation is complete and
        // successful.
        if self.dma_access.control != 0 {
            Err("fw_cfg DMA failed")
        } else {
            chunk.copy_from_slice(&self.dma_buf.data[..chunk.len()]);
            Ok(())
        }
    }
}

bitflags! {
    /// Control flags for DMA access.
    struct ControlFlags: u32 {
        /// Indicates that an error occurred during the DMA operation.
        const ERROR = 1 << 0;
        /// A DMA guest read operation is requested.
        const READ = 1 << 1;
    }
}

// Finds the highest section of RAM that is big enough to hold the DMA buffer,
// and falls below 1GiB.
pub fn find_suitable_dma_address(
    size: usize,
    e820_table: &[BootE820Entry],
) -> Result<PhysAddr, &'static str> {
    let padded_size = (size as u64).checked_next_multiple_of(Size4KiB::SIZE).unwrap();
    e820_table
        .iter()
        .filter_map(|entry| {
            if entry.entry_type() != Some(E820EntryType::RAM) {
                return None;
            }
            let start = entry.addr() as u64;
            let end = crate::TOP_OF_VIRTUAL_MEMORY.min(start + entry.size() as u64);
            if padded_size.checked_add(start).unwrap() > end {
                return None;
            }

            // Align the start address down in case the end was not aligned.
            Some(PhysAddr::new(end.checked_sub(padded_size).unwrap()).align_down(Size4KiB::SIZE))
        })
        .max_by(PhysAddr::cmp)
        .ok_or("no suitable memory available for dma buffer")
}

/// Ensures that two ranges don't overlap.
pub fn check_non_overlapping(
    range_1_start: VirtAddr,
    range_1_size: usize,
    range_2_start: VirtAddr,
    range_2_size: usize,
) -> Result<(), &'static str> {
    let range_1_end = range_1_start + (range_1_size as u64);
    let range_2_end = range_2_start + (range_2_size as u64);
    if range_1_start < range_2_end && range_1_end > range_2_start {
        return Err("regions overlap");
    }
    Ok(())
}

/// Definition for a DMA access request.
/// We also force it to be on a page boundary as we need to share it with the
/// host.
#[repr(C, align(4096))]
#[derive(Debug)]
pub struct FwCfgDmaAccess {
    control: u32,
    length: u32,
    address: u64,
    // Eat up the rest of the memory to ensure we're the only data structure on this page.
    padding: [u8; 4080],
}
static_assertions::assert_eq_size!(FwCfgDmaAccess, [u8; Size4KiB::SIZE as usize]);

impl Default for FwCfgDmaAccess {
    fn default() -> Self {
        FwCfgDmaAccess { control: 0, length: 0, address: 0, padding: [0u8; 4080] }
    }
}

impl FwCfgDmaAccess {
    const fn new(flags: ControlFlags, length: u32, address: PhysAddr) -> Self {
        // All the values in this structure is expected to be big endian encoded.
        FwCfgDmaAccess {
            control: flags.bits().to_be(),
            length: length.to_be(),
            address: address.as_u64().to_be(),
            padding: [0u8; 4080],
        }
    }
}

/// Interface for firmware functions that we need: namely, how to load the
/// configuration files.
///
/// This is effectively a subset of the `FwCfg` API that we need for building
/// tables.
pub trait Firmware {
    fn find(&mut self, name: &CStr) -> Option<DirEntry>;
    fn read_file(&mut self, file: &DirEntry, buf: &mut [u8]) -> Result<usize, &'static str>;
}

/// `FwCfg` is pretty much the canonical implementation of `Firmware` for our
/// use cases.
impl<P: crate::Platform> Firmware for FwCfg<P> {
    fn find(&mut self, name: &CStr) -> Option<DirEntry> {
        self.find(name)
    }

    fn read_file(&mut self, file: &DirEntry, buf: &mut [u8]) -> Result<usize, &'static str> {
        self.read_file(file, buf)
    }
}

#[cfg(test)]
#[derive(Default)]
pub struct TestFirmware {
    pub files: std::collections::BTreeMap<std::ffi::CString, Box<[u8]>>,
}

#[cfg(test)]
impl Firmware for TestFirmware {
    fn find(&mut self, name: &core::ffi::CStr) -> Option<crate::fw_cfg::DirEntry> {
        let file = self.files.get(name)?;
        Some(crate::fw_cfg::DirEntry::new(name, file.len() as u32, 0))
    }

    fn read_file(
        &mut self,
        file: &crate::fw_cfg::DirEntry,
        buf: &mut [u8],
    ) -> std::result::Result<usize, &'static str> {
        let file = self.files.get(file.name()).ok_or("file not found")?;
        buf.copy_from_slice(file);
        Ok(file.len())
    }
}
