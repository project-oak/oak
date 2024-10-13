//
// Copyright 2024 The Project Oak Authors
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

#![no_std]
#![no_main]

use core::{
    mem::{size_of, MaybeUninit},
    ops::{Index, IndexMut},
    panic::PanicInfo,
    sync::atomic::Ordering,
};

use log::info;
use oak_linux_boot_params::{BootE820Entry, E820EntryType};
use oak_stage0::paging::{self, PageEncryption};
use oak_tdx_guest::{
    tdcall::get_td_info,
    vmcall::{
        call_cpuid, io_read_u16, io_read_u32, io_read_u8, io_write_u16, io_write_u32, io_write_u8,
        mmio_read_u32, mmio_write_u32, msr_read, msr_write,
    },
};
use x86_64::{
    instructions::tlb,
    registers::control::Cr3,
    structures::paging::{
        frame::PhysFrameRange, page::NotGiantPageSize, OffsetPageTable, Page, PageSize, PageTable,
        PageTableFlags, PageTableIndex, PhysFrame, Size1GiB, Size2MiB, Size4KiB,
    },
    PhysAddr, VirtAddr,
};
use zerocopy::{AsBytes, FromBytes};
use zeroize::Zeroize;

mod asm;

mod counters {
    use core::sync::atomic::AtomicUsize;

    /// Number of FAIL_SIZEMISMATCH errors when invoking TDG.MEM.PAGE.ACCEPT on
    /// 2 MiB pages.
    pub static ERROR_FAIL_SIZE_MISMATCH: AtomicUsize = AtomicUsize::new(0);

    /// Number of successful TDG.MEM.PAGE.ACCEPT invocations on 2 MiB pages.
    pub static ACCEPTED_2M: AtomicUsize = AtomicUsize::new(0);

    /// Number of successful TDG.MEM.PAGE.ACCEPT invocations on 4 KiB pages.
    pub static ACCEPTED_4K: AtomicUsize = AtomicUsize::new(0);
}

#[no_mangle]
static mut TD_HOB_START: MaybeUninit<HandoffInfoTable> = MaybeUninit::uninit();

#[no_mangle]
static mut TD_MAILBOX_START: MaybeUninit<u32> = MaybeUninit::uninit();

#[no_mangle]
static mut GPAW: u32 = 0;

#[no_mangle]
static mut AP_IN_64BIT_COUNT: u32 = 0;

static HELLO_OAK: &str = "Hello from stage0_bin_tdx!";

const EFI_HOB_TYPE_HANDOFF: u16 = 0x0001;
const EFI_HOB_TYPE_RESOURCE_DESCRIPTOR: u16 = 0x0003;
const EFI_HOB_TYPE_END_OF_HOB_LIST: u16 = 0xFFFF;

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct Header {
    pub hob_type: u16,
    pub hob_length: u16,
    pub reserved: u32,
}

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct HandoffInfoTable {
    header: Header,
    version: u32,
    boot_mode: u32,
    memory_top: u64,
    memory_bottom: u64,
    free_memory_top: u64,
    free_memory_bottom: u64,
    end_of_hob_list: u64,
}

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct ResourceDescription {
    header: Header,
    owner: [u8; 16], // Guid
    resource_type: u32,
    resource_attribute: u32,
    physical_start: u64,
    resource_length: u64,
}

fn get_tdx_shared_bit() -> usize {
    unsafe { GPAW as usize - 1 }
}
// Inspired by TD-shim and credits to TD-shim
fn offset_pt() -> OffsetPageTable<'static> {
    let cr3 = Cr3::read().0.start_address().as_u64();
    unsafe { OffsetPageTable::new(&mut *(cr3 as *mut _), VirtAddr::new(0)) }
}

fn pt_entry_set_shared_bit(page_table: &mut PageTable, index: PageTableIndex, shared: bool) {
    let entry = page_table.index(index);
    let shared_bit = 1 << get_tdx_shared_bit();

    let addr = if shared {
        entry.addr().as_u64() | shared_bit
    } else {
        entry.addr().as_u64() & !shared_bit
    };
    let flags = entry.flags();

    page_table.index_mut(index).set_addr(PhysAddr::new(addr), flags);
}

// TODO: b/360129756 - simplify this function. consider merging it into stage0
fn pt_set_shared_bit(pt: &mut OffsetPageTable, page: &Page, shared: bool) {
    let p4 = pt.level_4_table();
    let p3 = unsafe { &mut *(p4.index(page.p4_index()).addr().as_u64() as *mut PageTable) };

    if page.size() == Size1GiB::SIZE {
        pt_entry_set_shared_bit(p3, page.p3_index(), shared);
    }

    let p2 = unsafe { &mut *(p3.index(page.p3_index()).addr().as_u64() as *mut PageTable) };
    if page.size() == Size2MiB::SIZE {
        pt_entry_set_shared_bit(p2, page.p2_index(), shared);
    }

    let p1 = unsafe { &mut *(p2.index(page.p2_index()).addr().as_u64() as *mut PageTable) };
    if page.size() == Size4KiB::SIZE {
        pt_entry_set_shared_bit(p1, page.p1_index(), shared);
    }
}

trait TdAcceptPage {
    fn accept_page(&self) -> Result<(), &'static str>;
}

impl<S: NotGiantPageSize + oak_tdx_guest::tdcall::TdxSize> TdAcceptPage for PhysFrameRange<S> {
    fn accept_page(&self) -> Result<(), &'static str> {
        for frame in *self {
            if frame.size() == 4096 {
                oak_tdx_guest::tdcall::accept_memory(frame).expect("map 4k cannot fail");
                counters::ACCEPTED_4K.fetch_add(1, Ordering::SeqCst);
            } else {
                use oak_tdx_guest::tdcall::AcceptMemoryError;
                match oak_tdx_guest::tdcall::accept_memory(frame) {
                    Ok(()) => {
                        counters::ACCEPTED_2M.fetch_add(1, Ordering::SeqCst);
                    }
                    Err(AcceptMemoryError::AlreadyAccepted) => continue,
                    Err(AcceptMemoryError::PageSizeMisMatch) => {
                        // cannot accept as 2MiB. let's try 4KiB
                        counters::ERROR_FAIL_SIZE_MISMATCH.fetch_add(1, Ordering::SeqCst);
                        let start_addr_u64 = frame.start_address().as_u64();
                        let limit_addr_u64 = start_addr_u64 + 2 * 1024 * 1024;
                        let start_address = PhysAddr::new(start_addr_u64);
                        let limit = PhysAddr::new(limit_addr_u64);
                        let range = PhysFrame::<Size4KiB>::range(
                            PhysFrame::from_start_address(start_address).unwrap(),
                            PhysFrame::from_start_address(limit).unwrap(),
                        );
                        range.accept_page().unwrap();
                    }
                    _ => {
                        // InvalidOperandInRcx or OperandBusy
                        panic!("oops");
                    }
                }
            }
        }

        Ok(())
    }
}

fn write_u8_to_serial(c: u8) {
    // wait_for_empty_output
    loop {
        if (io_read_u8(0x3f8 + 0x5).unwrap() & (1 << 5)) != 0 {
            break;
        }
    }
    io_write_u8(0x3f8, c).unwrap();
}

fn write_single_hex(c: u8) {
    if c < 0xa {
        write_u8_to_serial(c + (b'0'));
    } else {
        write_u8_to_serial(c - 10 + (b'a'));
    }
}

fn write_byte_hex(c: u8) {
    let char1 = (c >> 4) & 0xF;
    let char2 = c & 0xF;
    write_single_hex(char1);
    write_single_hex(char2);
}

fn write_u32(n: u32) {
    let b = n.to_le_bytes();
    for c in b.iter().rev() {
        write_byte_hex(*c);
    }
    write_u8_to_serial(b'\n');
}

fn write_u64(n: u64) {
    let b = n.to_le_bytes();
    for c in b.iter().rev() {
        write_byte_hex(*c);
    }
    write_u8_to_serial(b'\n');
}

fn write_str(s: &str) {
    for c in s.bytes() {
        write_u8_to_serial(c);
    }
    write_u8_to_serial(b'\n');
}

fn debug_u32_variable(s: &str, val: u32) {
    for c in s.bytes() {
        write_u8_to_serial(c);
    }
    write_u8_to_serial(b':');
    write_u8_to_serial(b' ');
    write_u32(val);
}

fn debug_u64_variable(s: &str, val: u64) {
    for c in s.bytes() {
        write_u8_to_serial(c);
    }
    write_u8_to_serial(b':');
    write_u8_to_serial(b' ');
    write_u64(val);
}

fn init_tdx_serial_port() {
    io_write_u8(0x3f8 + 0x1, 0x0).unwrap(); // Disable interrupts
    io_write_u8(0x3f8 + 0x2, 0x0).unwrap(); // Disable FIFO
    io_write_u8(0x3f8 + 0x3, 0x3).unwrap(); // LINE_CONTROL_8N1
    io_write_u8(0x3f8 + 0x4, 0x3).unwrap(); // DATA_TERMINAL_READY_AND_REQUEST_TO_SEND
}

use oak_stage0::hal::PortFactory;

struct Mmio {}
impl<S: x86_64::structures::paging::page::PageSize> oak_stage0::hal::Mmio<S> for Mmio {
    fn read_u32(&self, offset: usize) -> u32 {
        mmio_read_u32(offset as *const u32).unwrap()
    }
    unsafe fn write_u32(&mut self, offset: usize, val: u32) {
        mmio_write_u32(offset as *mut u32, val).unwrap()
    }
}

struct Tdx {}

impl oak_stage0::Platform for Tdx {
    type Mmio<S: x86_64::structures::paging::page::PageSize> = Mmio;
    fn cpuid(leaf: u32) -> core::arch::x86_64::CpuidResult {
        call_cpuid(leaf, 0).unwrap()
    }

    unsafe fn mmio<S>(_: x86_64::addr::PhysAddr) -> <Self as oak_stage0::Platform>::Mmio<S>
    where
        S: x86_64::structures::paging::page::PageSize,
    {
        todo!()
    }

    fn port_factory() -> PortFactory {
        PortFactory {
            read_u8: |port| io_read_u8(port as u32),
            read_u16: |port| io_read_u16(port as u32),
            read_u32: |port| io_read_u32(port as u32),
            write_u8: |port, val| io_write_u8(port as u32, val),
            write_u16: |port, val| io_write_u16(port as u32, val),
            write_u32: |port, val| io_write_u32(port as u32, val),
        }
    }

    fn early_initialize_platform() {
        write_str("early_initialize_platform");
        write_str("early_initialize_platform completed");
    }

    fn prefill_e820_table<T: AsBytes + FromBytes>(dest: &mut T) -> Result<usize, &'static str> {
        write_str("Prefill e820 table from TDHOB");

        let hit = unsafe { TD_HOB_START.assume_init() };
        debug_u32_variable("HOB TYPE", hit.header.hob_type as u32);
        debug_u32_variable("HOB LENGTH", hit.header.hob_length as u32);
        debug_u32_variable("HOB VERSION", hit.version);
        debug_u32_variable("HOB BOOT MODE", hit.boot_mode);
        debug_u64_variable("HOB MEMORY TOP", hit.memory_top);
        debug_u64_variable("HOB MEMORY BOTTOM", hit.memory_bottom);
        debug_u64_variable("HOB FREE MEMORY TOP", hit.free_memory_top);
        debug_u64_variable("HOB FREE MEMORY BOTTOM", hit.free_memory_bottom);
        debug_u64_variable("HOB END OF HOB LIST", hit.end_of_hob_list);

        if hit.header.hob_length as usize != size_of::<HandoffInfoTable>()
            || hit.header.hob_type != EFI_HOB_TYPE_HANDOFF
        {
            return Err("Corrupted TD HoB header");
        }

        let mut curr_ptr = unsafe {
            TD_HOB_START.as_ptr().byte_offset(hit.header.hob_length as isize) as *const Header
        };
        let mut curr_hdr = unsafe { *curr_ptr };
        let mut index = 0;

        while (curr_ptr as u64) < hit.end_of_hob_list {
            // Every HoB entry starts with a Header struct
            write_str("==================");
            debug_u32_variable("HOB PTR", curr_ptr as u32);
            debug_u32_variable("HOB TYPE", curr_hdr.hob_type as u32);
            debug_u32_variable("HOB LENGTH", curr_hdr.hob_length as u32);

            // We only care the resource descriptor entries
            if curr_hdr.hob_type == EFI_HOB_TYPE_RESOURCE_DESCRIPTOR && curr_hdr.hob_length == 0x30
            {
                let curr_src = unsafe { *(curr_ptr as *const ResourceDescription) };
                debug_u32_variable("Resource type", curr_src.resource_type);
                debug_u32_variable("Resource attribute", curr_src.resource_attribute);
                debug_u64_variable("Physical start", curr_src.physical_start);
                debug_u64_variable("Resource length", curr_src.resource_length);

                // Figure out the location of the next E820 entry
                let new_entry_ptr: *mut BootE820Entry = unsafe {
                    dest.as_bytes_mut().as_mut_ptr().byte_add(index) as *mut BootE820Entry
                };

                let entry_type = if curr_src.physical_start
                    == unsafe { TD_HOB_START.as_ptr() as u64 }
                {
                    E820EntryType::NVS // is this correct?
                } else if curr_src.physical_start == unsafe { TD_MAILBOX_START.as_ptr() as u64 } {
                    E820EntryType::NVS // ditto
                } else if curr_src.physical_start == 0 {
                    // [0x0, 512KB) is usable
                    E820EntryType::RAM
                } else if curr_src.resource_type == 0 {
                    // [0xF_0000, 0x10_0000)
                    E820EntryType::RESERVED
                } else {
                    E820EntryType::RAM
                };

                unsafe {
                    *new_entry_ptr = BootE820Entry::new(
                        curr_src.physical_start as usize,
                        curr_src.resource_length as usize,
                        entry_type,
                    );
                }
                index = index + size_of::<BootE820Entry>();
            } else if curr_hdr.hob_type == EFI_HOB_TYPE_END_OF_HOB_LIST {
                // reached at the end
            } else {
                return Err("Unknown resource type found in TD HoB");
            }
            curr_ptr = unsafe { curr_ptr.byte_offset(curr_hdr.hob_length as isize) };
            curr_hdr = unsafe { *curr_ptr };
        }
        if index == 0 { Err("no valid TD HoB found") } else { Ok(index) }
    }

    fn initialize_platform(e820_table: &[oak_linux_boot_params::BootE820Entry]) {
        // logger is initialized starting from here
        info!("initialize platform");
        info!("{:?}", e820_table);
        info!("starting TDX memory acceptance");
        let mut page_tables = paging::PAGE_TABLE_REFS.get().unwrap().lock();
        let accept_pd_pt = PageTable::new();
        if page_tables.pdpt[1].flags().contains(PageTableFlags::PRESENT) {
            panic!("PDPT[1] is in use");
        }

        page_tables.pdpt[1].set_address::<Tdx>(
            PhysAddr::new(&accept_pd_pt as *const _ as u64),
            PageTableFlags::PRESENT,
            PageEncryption::Encrypted,
        );
        info!("added pdpt[1]");

        info!("adding pd_0[1]");
        let accept_pt_pt = PageTable::new();
        if page_tables.pd_0[1].flags().contains(PageTableFlags::PRESENT) {
            panic!("PD_0[1] is in use");
        }
        page_tables.pd_0[1].set_address::<Tdx>(
            PhysAddr::new(&accept_pt_pt as *const _ as u64),
            PageTableFlags::PRESENT,
            PageEncryption::Encrypted,
        );
        info!("added pd_0[1]");

        let min_addr = 0xA0000;

        // TODO: b/360256588 - use TD-HoB to replace the e820_table here
        for entry in e820_table {
            if entry.entry_type() != Some(E820EntryType::RAM) || entry.addr() < min_addr {
                continue;
            }

            let start_address = PhysAddr::new(entry.addr() as u64).align_up(Size4KiB::SIZE);
            let limit_address =
                PhysAddr::new((entry.addr() + entry.size()) as u64).align_down(Size4KiB::SIZE);

            if start_address > limit_address {
                log::error!(
                    "nonsensical entry in E820 table: [{}, {})",
                    entry.addr(),
                    entry.addr() + entry.size()
                );
                continue;
            }

            // Attempt to validate as many pages as possible using 2 MiB pages (aka
            // hugepages).
            let hugepage_start = start_address.align_up(Size2MiB::SIZE);
            let hugepage_limit = limit_address.align_down(Size2MiB::SIZE);

            // If start_address == hugepage_start, we're aligned with 2M address boundary.
            // Otherwise, we need to process any 4K pages before the alignment.
            // Note that limit_address may be less than hugepage_start, which means that the
            // E820 entry was less than 2M in size and didn't cross a 2M boundary.
            if hugepage_start > start_address {
                let limit = core::cmp::min(hugepage_start, limit_address);
                // We know the addresses are aligned to at least 4K, so the unwraps are safe.
                let range = PhysFrame::<Size4KiB>::range(
                    PhysFrame::from_start_address(start_address).unwrap(),
                    PhysFrame::from_start_address(limit).unwrap(),
                );
                range.accept_page().unwrap();
            }

            // If hugepage_limit > hugepage_start, we've got some contiguous 2M chunks that
            // we can process as hugepages.
            if hugepage_limit > hugepage_start {
                // These unwraps can't fail as we've made sure that the addresses are 2
                // MiB-aligned.
                let range = PhysFrame::<Size2MiB>::range(
                    PhysFrame::from_start_address(hugepage_start).unwrap(),
                    PhysFrame::from_start_address(hugepage_limit).unwrap(),
                );
                range.accept_page().unwrap();
            }
            // And finally, we may have some trailing 4K pages in [hugepage_limit,
            // limit_address) that we need to process.
            if limit_address > hugepage_limit {
                let start = core::cmp::max(start_address, hugepage_limit);
                // We know the addresses are aligned to at least 4K, so the unwraps are safe.
                let range = PhysFrame::<Size4KiB>::range(
                    PhysFrame::from_start_address(start).unwrap(),
                    PhysFrame::from_start_address(limit_address).unwrap(),
                );
                range.accept_page().unwrap();
            }
        }
        // Locate the legacy SMBIOS range [0xF_0000, 0x10_0000) in the E820 table.
        // Unwrap() will panic if entry not found with expected start, size, and type.
        let legacy_smbios_range_entry = e820_table
            .iter()
            .find(|entry| {
                entry.addr() == 0xF_0000
                    && entry.size() == 0x1_0000
                    && entry.entry_type() == Some(E820EntryType::RESERVED)
            })
            .expect("couldn't find legacy SMBIOS memory range");

        // Pvalidate the legacy SMBIOS range since legacy code may scan this range for
        // the SMBIOS entry point table, even if the range is marked as reserved.
        let range = PhysFrame::<Size4KiB>::range(
            PhysFrame::from_start_address(PhysAddr::new(legacy_smbios_range_entry.addr() as u64))
                .unwrap(),
            PhysFrame::from_start_address(PhysAddr::new(
                (legacy_smbios_range_entry.addr() + legacy_smbios_range_entry.size()) as u64,
            ))
            .unwrap(),
        );
        range.accept_page().expect("failed to validate SMBIOS memory");

        // Safety: the E820 table indicates that this is the correct memory segment.
        let legacy_smbios_range_bytes = unsafe {
            core::slice::from_raw_parts_mut::<u8>(
                legacy_smbios_range_entry.addr() as *mut u8,
                legacy_smbios_range_entry.size(),
            )
        };
        // Zeroize the legacy SMBIOS range bytes to avoid legacy code reading garbage.
        legacy_smbios_range_bytes.zeroize();
        page_tables.pd_0[1].set_unused();
        page_tables.pdpt[1].set_unused();
        tlb::flush_all();

        log::info!("TDX memory acceptance complete.");
        log::info!(
            "  Accepted using 2 MiB pages: {}",
            counters::ACCEPTED_2M.load(Ordering::SeqCst)
        );
        log::info!(
            "  Accepted using 4 KiB pages: {}",
            counters::ACCEPTED_4K.load(Ordering::SeqCst)
        );
        log::info!(
            "  TDX page size mismatch errors (fallback to 4K): {}",
            counters::ERROR_FAIL_SIZE_MISMATCH.load(Ordering::SeqCst)
        );

        info!("initialize platform completed");
    }

    fn deinit_platform() {
        //TODO: b/360488922 - impl deinit_platform
    }
    fn populate_zero_page(_: &mut oak_stage0::ZeroPage) {
        info!("populate_zero_page start");
        info!("populate_zero_page completed");
    }
    fn get_attestation(
        _: [u8; 64],
    ) -> Result<oak_sev_snp_attestation_report::AttestationReport, &'static str> {
        //TODO: b/360488295 - impl get_attestation
        Ok(oak_sev_snp_attestation_report::AttestationReport::from_report_data([0; 64]))
    }
    fn get_derived_key() -> Result<[u8; 32], &'static str> {
        // TODO: b/360488668 - impl get_derived_key
        Ok([0; 32])
    }
    fn change_page_state(
        page: x86_64::structures::paging::Page,
        attr: oak_stage0::hal::PageAssignment,
    ) {
        let shared: bool = match attr {
            oak_stage0::hal::PageAssignment::Shared => true,
            oak_stage0::hal::PageAssignment::Private => false,
        };
        let mut pt = offset_pt();
        pt_set_shared_bit(&mut pt, &page, shared);
    }
    fn revalidate_page(_: x86_64::structures::paging::Page) {
        // TODO: b/360488924 - impl revalidate_page
    }
    fn page_table_mask(enc: oak_stage0::paging::PageEncryption) -> u64 {
        // a. When 4-level EPT is active, the SHARED bit position would
        // always be bit 47.
        // b. When 5-level EPT is active, the SHARED bit position would
        // be bit 47 if GPAW is 0. Otherwise, else it would be bit 51.
        match enc {
            oak_stage0::paging::PageEncryption::Encrypted => 0,
            oak_stage0::paging::PageEncryption::Unencrypted => 1 << get_tdx_shared_bit(),
        }
    }
    fn encrypted() -> u64 {
        // stage0_bin_tdx does not support regular VM
        1 << get_tdx_shared_bit()
    }
    fn tee_platform() -> oak_dice::evidence::TeePlatform {
        oak_dice::evidence::TeePlatform::IntelTdx
    }
    unsafe fn read_msr(msr: u32) -> u64 {
        msr_read(msr).unwrap()
    }
    unsafe fn write_msr(msr: u32, value: u64) {
        msr_write(msr, value).unwrap()
    }
}

/// Entry point for the Rust code in the stage0 BIOS.
#[no_mangle]
pub extern "C" fn rust64_start() -> ! {
    init_tdx_serial_port();
    write_str(HELLO_OAK);
    debug_u32_variable(stringify!(GPAW), unsafe { GPAW });
    assert!(unsafe { GPAW == 48 || GPAW == 52 });

    let td_info = get_td_info();
    debug_u64_variable(stringify!(td_info.gpa_width), td_info.gpa_width as u64);
    debug_u64_variable(stringify!(td_info.attributes), td_info.attributes.bits() as u64);
    debug_u32_variable(stringify!(td_info.max_vcpus), td_info.max_vcpus);
    debug_u32_variable(stringify!(td_info.num_vcpus), td_info.num_vcpus);
    debug_u32_variable(stringify!(AP_IN_64BIT_COUNT), unsafe { AP_IN_64BIT_COUNT });
    debug_u32_variable(stringify!(FIRST_DWORD_OF_MAILBOX), unsafe { *TD_MAILBOX_START.as_ptr() });

    oak_stage0::rust64_start::<Tdx>()
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    oak_stage0::panic(info)
}
