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

extern crate alloc;

use alloc::boxed::Box;
use core::{
    mem::size_of,
    ops::{Index, IndexMut},
    pin::pin,
    ptr::addr_of,
    sync::atomic::Ordering,
};

use log::info;
use oak_hal::{MsrAccess, PageAssignment, PageEncryption, Platform};
use oak_linux_boot_params::{BootE820Entry, E820EntryType};
use oak_stage0::{
    AcpiTables, BOOT_ALLOC, Madt,
    hal::{FirmwarePlatform, PortFactory},
    mailbox::{FirmwareMailbox, OsMailbox},
    paging::{self, PageTableRefs},
};
use oak_tdx_guest::{
    tdcall::get_td_info,
    vmcall::{call_cpuid, msr_read, msr_write, tdvmcall_wbinvd},
};
use serial::Debug;
use x86_64::{
    PhysAddr, VirtAddr,
    instructions::tlb,
    registers::control::Cr3,
    structures::paging::{
        OffsetPageTable, Page, PageSize, PageTable, PageTableFlags, PageTableIndex, PhysFrame,
        Size1GiB, Size2MiB, Size4KiB,
    },
};
use zerocopy::{FromBytes, IntoBytes};
use zeroize::Zeroize;

use crate::{
    accept_memory::{TdAcceptPage, accept_memory_range, counters},
    hob::{self, ResourceDescription},
    mmio::Mmio,
    serial,
};

/// Firmware Mailbox.
///
/// This structure is part of the firmware, it's declared in layout.ld .
/// This mailbox is used for communication between BSP and APs (CPUs) while
/// still running firmware (stage0) code. The OS will not have access to it.
/// In order to hand APs off to the OS, the BSP needs to create a second
/// mailbox (OS mailbox). It uses the firmware mailbox to tell APs where the
/// OS mailbox is.
#[unsafe(link_section = ".tdx.td_mailbox")]
static mut TD_MAILBOX: FirmwareMailbox = FirmwareMailbox::new();
const TD_MAILBOX_LOCATION: u64 = 0x102000; // Keep in sync with layout.ld.

#[unsafe(no_mangle)]
static mut GPAW: u32 = 0;

#[unsafe(no_mangle)]
static mut AP_IN_64BIT_COUNT: i32 = 0;

static HELLO_OAK: &str = "Hello from stage0_bin_tdx!";

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

/// Prints debug messages of the raw contents of the memory where
/// TD_MAILBOX_START is. (See: [`stage0::mailbox::FirmwareMailbox`])
///
/// Given the firmware mailbox is processed from assembly code (tdx.s,
/// _ap_poll_firmware_mailbox), we are interested in seeing the exact raw
/// contents, not what Rust might interpret of them.
fn debug_print_td_mailbox() {
    serial::debug!("ADDR_OF_TD_MAILBOX: ", addr_of!(TD_MAILBOX) as u64);
    // Safety: TD_MAILBOX_START points to valid TEMPMEM memory as defined
    // in layout.ld. The VMM allocates this temporary memory for us.
    // Safe because we are only reading the first 16 bytes out of TD_MAILBOX_SIZE
    // (4k).
    serial::debug!("TD_MAILBOX FIRST QUAD (is_address_set): ", unsafe {
        *(addr_of!(TD_MAILBOX) as *const u64)
    });
    serial::debug!("TD_MAILBOX SECOND QUAD (os_mailbox_address): ", unsafe {
        *(addr_of!(TD_MAILBOX).byte_add(8) as *const u64)
    });
}

fn show_td_info() {
    serial::init_tdx_serial_port();
    serial::debug!(HELLO_OAK);
    serial::debug!("GPAW: ", unsafe { GPAW });
    assert!(unsafe { GPAW == 48 || GPAW == 52 });

    let td_info = get_td_info();
    serial::debug!("td_info.gpa_width: ", td_info.gpa_width as u64);
    serial::debug!("td_info.gpa_width: ", td_info.gpa_width as u64);
    serial::debug!("td_info.attributes: ", td_info.attributes.bits());
    serial::debug!("td_info.max_vcpus: ", td_info.max_vcpus);
    serial::debug!("td_info.num_vcpus: ", td_info.num_vcpus);
    serial::debug!("AP_IN_64BIT_COUNT: ", unsafe { AP_IN_64BIT_COUNT as u32 });
    debug_print_td_mailbox();
}

fn setup_mailbox() {
    assert!(addr_of!(TD_MAILBOX) as u64 == TD_MAILBOX_LOCATION, "TD Mailbox is misplaced");
    info!("Creating OS Mailbox");
    let os_mailbox = Box::new_in(OsMailbox::default(), &BOOT_ALLOC);
    let os_mailbox_ptr = Box::leak(os_mailbox) as *const OsMailbox; // Let the allocator forget about it so it never deallocates it.

    // Use the firmware mailbox to tell APs where the OS mailbox is.
    // Safety: this is the only access to the structure at TD_MAILBOX_START.
    unsafe { TD_MAILBOX.set_os_mailbox_address(os_mailbox_ptr as u64) };

    info!("OS Mailbox created and its address passed to APs via TD Mailbox");
    debug_print_td_mailbox();
}

fn init_tdx_page_tables() -> lock_api::MutexGuard<'static, spinning_top::RawSpinlock, PageTableRefs>
{
    let mut page_tables = paging::PAGE_TABLE_REFS.get().unwrap().lock();
    let accept_pd_pt = pin!(oak_stage0::paging::PageTable::new());
    if page_tables.pdpt[1].flags().contains(PageTableFlags::PRESENT) {
        panic!("PDPT[1] is in use");
    }

    page_tables.pdpt[1]
        .set_lower_level_table::<Tdx>(accept_pd_pt.as_ref(), PageTableFlags::PRESENT);
    info!("added pdpt[1]");

    info!("adding pd_0[1]");
    let accept_pt_pt = pin!(oak_stage0::paging::PageTable::new());
    if page_tables.pd_0[1].flags().contains(PageTableFlags::PRESENT) {
        panic!("PD_0[1] is in use");
    }
    page_tables.pd_0[1]
        .set_lower_level_table::<Tdx>(accept_pt_pt.as_ref(), PageTableFlags::PRESENT);
    info!("added pd_0[1]");
    page_tables
}

fn accept_tdx_memory(e820_table: &[oak_linux_boot_params::BootE820Entry]) {
    info!("starting TDX memory acceptance");
    // Initialize page tables for TDX memory acceptance.
    let mut page_tables = init_tdx_page_tables();
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
        accept_memory_range(start_address, limit_address);
    }

    page_tables.pd_0[1].set_unused();
    page_tables.pdpt[1].set_unused();
    tlb::flush_all();

    log::info!("TDX memory acceptance complete.");
    log::info!("  Accepted using 2 MiB pages: {}", counters::ACCEPTED_2M.load(Ordering::SeqCst));
    log::info!("  Accepted using 4 KiB pages: {}", counters::ACCEPTED_4K.load(Ordering::SeqCst));
    log::info!(
        "  TDX page size mismatch errors (fallback to 4K): {}",
        counters::ERROR_FAIL_SIZE_MISMATCH.load(Ordering::SeqCst)
    );
}

fn handle_legacy_smbios(e820_table: &[oak_linux_boot_params::BootE820Entry]) {
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

    // Accept the legacy SMBIOS range since legacy code may scan this range for
    // the SMBIOS entry point table, even if the range is marked as reserved.
    let range = PhysFrame::<Size4KiB>::range(
        PhysFrame::from_start_address(PhysAddr::new(legacy_smbios_range_entry.addr() as u64))
            .unwrap(),
        PhysFrame::from_start_address(PhysAddr::new(
            (legacy_smbios_range_entry.addr() + legacy_smbios_range_entry.size()) as u64,
        ))
        .unwrap(),
    );
    range.accept_page().expect("failed to accept SMBIOS memory");

    // Safety: the E820 table indicates that this is the correct memory segment.
    let legacy_smbios_range_bytes = unsafe {
        core::slice::from_raw_parts_mut::<u8>(
            legacy_smbios_range_entry.addr() as *mut u8,
            legacy_smbios_range_entry.size(),
        )
    };
    // Zeroize the legacy SMBIOS range bytes to avoid legacy code reading garbage.
    legacy_smbios_range_bytes.zeroize();
}

pub struct Tdx {}

impl Platform for Tdx {
    type Mmio = Mmio;

    fn cpuid(leaf: u32) -> core::arch::x86_64::CpuidResult {
        call_cpuid(leaf, 0).unwrap()
    }

    unsafe fn mmio(_: x86_64::addr::PhysAddr) -> <Self as Platform>::Mmio {
        todo!()
    }

    fn port_factory() -> PortFactory {
        serial::port_factory()
    }

    fn early_initialize_platform() {
        show_td_info();
        serial::debug!("early_initialize_platform completed");
    }

    fn initialize_platform(e820_table: &[oak_linux_boot_params::BootE820Entry]) {
        // logger is initialized starting from here
        info!("initialize platform");
        info!("{:?}", e820_table);

        setup_mailbox();
        accept_tdx_memory(e820_table);
        handle_legacy_smbios(e820_table);

        info!("initialize platform completed");
    }

    fn change_page_state(page: x86_64::structures::paging::Page, attr: PageAssignment) {
        let shared: bool = match attr {
            PageAssignment::Shared => true,
            PageAssignment::Private => false,
        };
        let mut pt = offset_pt();
        pt_set_shared_bit(&mut pt, &page, shared);
    }

    fn revalidate_page(_: x86_64::structures::paging::Page) {
        // TODO: b/360488924 - impl revalidate_page
    }

    fn page_table_mask(enc: PageEncryption) -> u64 {
        // a. When 4-level EPT is active, the SHARED bit position would
        // always be bit 47.
        // b. When 5-level EPT is active, the SHARED bit position would
        // be bit 47 if GPAW is 0. Otherwise, else it would be bit 51.
        match enc {
            PageEncryption::Unset => 0,
            PageEncryption::Encrypted => 0,
            PageEncryption::Unencrypted => 1 << get_tdx_shared_bit(),
        }
    }

    fn encrypted() -> u64 {
        // stage0_bin_tdx does not support regular VM
        1 << get_tdx_shared_bit()
    }

    fn wbvind() {
        tdvmcall_wbinvd().unwrap()
    }
}

impl FirmwarePlatform for Tdx {
    type Attester = crate::attestation::RtmrAttester;

    #[allow(clippy::if_same_then_else)]
    fn prefill_e820_table<T: IntoBytes + FromBytes>(dest: &mut T) -> Result<usize, &'static str> {
        serial::debug!("Prefill e820 table from TDHOB");

        let hit = hob::get_hit()?;
        let mut index = 0;

        for curr_ptr in hit.into_iter() {
            let curr_hdr = unsafe { *curr_ptr };
            // Every HoB entry starts with a Header struct
            serial::debug!("==================");
            serial::debug!("HOB PTR: ", curr_ptr as u32);
            serial::debug!("HOB TYPE: ", curr_hdr.hob_type as u32);
            serial::debug!("HOB LENGTH: ", curr_hdr.hob_length as u32);

            // We only care the resource descriptor entries
            if curr_hdr.is_resource_descriptor() {
                let curr_src = unsafe { *(curr_ptr as *const ResourceDescription) };
                serial::debug!("Resource type: ", curr_src.resource_type);
                serial::debug!("Resource attribute: ", curr_src.resource_attribute);
                serial::debug!("Physical start: ", curr_src.physical_start);
                serial::debug!("Resource length: ", curr_src.resource_length);

                // Figure out the location of the next E820 entry
                let new_entry_ptr: *mut BootE820Entry = unsafe {
                    dest.as_mut_bytes().as_mut_ptr().byte_add(index) as *mut BootE820Entry
                };

                let entry_type = if curr_src.physical_start == hob::get_hob_start() as u64 {
                    E820EntryType::NVS // is this correct?
                } else if curr_src.physical_start == (addr_of!(TD_MAILBOX) as u64) {
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
                index += size_of::<BootE820Entry>();
            } else if curr_hdr.is_end_of_hob_list() {
                // reached at the end
            } else {
                return Err("Unknown resource type found in TD HoB");
            }
        }
        if index == 0 { Err("no valid TD HoB found") } else { Ok(index) }
    }

    fn finalize_acpi_tables(tables: &mut AcpiTables) -> Result<(), &'static str> {
        // In TDX, we need add a MultiprocessorWakeupStructure (ACPI specification table
        // 5.43) entry with the OS Mailbox Address to the MADT table. If
        // the MADT is not the last structure, then we need to move it down so
        // that it is the last one, where it has space to grow.

        // We assume that TD_MAILBOX has been initialized by `initialize_platform`.
        // Safety: Only BSP writes to mailbox and uses atomics.
        let os_mailbox_address = unsafe {
            TD_MAILBOX
                .get_os_mailbox_address()
                .expect("Expected TD_MAILBOX to contain OS Mailbox address")
        };

        let mut new_madt_buf = None;
        if let Some(madt) = tables.try_find_table_mut::<Madt>()? {
            info!("Finalize ACPI: Found a MADT in RSDT/XSDT.");
            // Safety: The header is in the ACPI memory range, guaranteed by `AcpiTables`,
            // so it's safe to attempt this transmute.
            let old_madt_addr = madt.as_bytes().as_ptr();
            info!("Finalize ACPI: Found a MADT at {:?}", madt.as_bytes().as_ptr_range());
            let new_madt = madt.set_or_append_mp_wakeup(os_mailbox_address)?;

            if old_madt_addr != new_madt.as_bytes().as_ptr() {
                // MADT was relocated
                //
                // Safety: This is bit of a hack. Ideally we'd use something like
                // `IntoBytes::as_mut_bytes()` for this, but `Madt` is not `FromBytes` (it's
                // `TryFromBytes`, because of the header). Zerocopy insists on `FromBytes`, as
                // that's a way to guarantee that even if you change something in the raw byte
                // buffer, the `Madt` stays valid.
                //
                // Our situation here is different: we won't treat `new_madt` as a `Madt` after
                // this, so changing the buffer is okay.
                new_madt_buf = Some((VirtAddr::from_ptr(old_madt_addr), unsafe {
                    core::slice::from_raw_parts_mut(
                        new_madt as *mut _ as *mut u8,
                        size_of_val(new_madt),
                    )
                }));
            }
        } else {
            return Err(
                "Could not find a MADT where to update or add a Multiprocessor Wakeup structure.",
            );
        }

        if let Some((old_madt_addr, new_madt)) = new_madt_buf {
            let new_madt_addr = VirtAddr::from_ptr(new_madt);
            tables.add_buffer(new_madt);
            tables.replace_table_ref(old_madt_addr, new_madt_addr)?;
        }

        Ok(())
    }

    fn deinit_platform() {
        //TODO: b/360488922 - impl deinit_platform
    }

    fn populate_zero_page(_: &mut oak_stage0::ZeroPage) {
        info!("populate_zero_page start");
        info!("populate_zero_page completed");
    }

    fn get_attester() -> Result<Self::Attester, &'static str> {
        Ok(crate::attestation::RtmrAttester::default())
    }

    fn get_derived_key() -> Result<[u8; 32], &'static str> {
        // TODO: b/360488668 - impl get_derived_key
        Ok([0; 32])
    }

    fn tee_platform() -> oak_dice::evidence::TeePlatform {
        oak_dice::evidence::TeePlatform::IntelTdx
    }
}

impl MsrAccess for Tdx {
    unsafe fn read_msr(msr: u32) -> u64 {
        msr_read(msr).unwrap()
    }
    unsafe fn write_msr(msr: u32, value: u64) {
        unsafe { msr_write(msr, value).unwrap() }
    }
}
