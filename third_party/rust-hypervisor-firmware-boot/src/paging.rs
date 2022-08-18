extern crate log;

use x86_64::{
    registers::control::Cr3,
    structures::paging::{PageSize, PageTable, PageTableFlags, PhysFrame, Size2MiB},
    PhysAddr,
};

// Amount of memory we identity map in setup(), max 512 GiB.
const ADDRESS_SPACE_GIB: usize = 4;
const TABLE: PageTable = PageTable::new();

// Put the Page Tables in static muts to make linking easier
#[no_mangle]
static mut L4_TABLE: PageTable = PageTable::new();
#[no_mangle]
static mut L3_TABLE: PageTable = PageTable::new();
#[no_mangle]
static mut L2_TABLES: [PageTable; ADDRESS_SPACE_GIB] = [TABLE; ADDRESS_SPACE_GIB];

pub fn setup() {
    // SAFETY: This function is idempontent and only writes to static memory and
    // CR3. Thus, it is safe to run multiple times or on multiple threads.
    let (l4, l3, l2s) = unsafe { (&mut L4_TABLE, &mut L3_TABLE, &mut L2_TABLES) };
    log::info!("Setting up {} GiB identity mapping", ADDRESS_SPACE_GIB);
    let pt_flags = PageTableFlags::PRESENT | PageTableFlags::WRITABLE;

    // Setup Identity map using L2 huge pages
    let mut next_addr = PhysAddr::new(0);
    for l2 in l2s.iter_mut() {
        for l2e in l2.iter_mut() {
            l2e.set_addr(next_addr, pt_flags | PageTableFlags::HUGE_PAGE);
            next_addr += Size2MiB::SIZE;
        }
    }

    // Point L3 at L2s
    for (i, l2) in l2s.iter().enumerate() {
        l3[i].set_addr(phys_addr(l2), pt_flags);
    }
    // Upper half hack.
    let addr_0 = l3[0].addr();
    let addr_1 = l3[1].addr();
    l3[510].set_addr(addr_0, pt_flags);
    l3[511].set_addr(addr_1, pt_flags);

    // Upper half hack: we point the last two entries of the L3 table to the same L2 tables as the
    // first two entries, and then we point to the last entry of the L4 table to the same L3 table
    // as the first entry in the L4 table. This means we get an extra identity-mapped region at
    // -2GB of virtual memory, where the kernel will live.
    let addr_0 = l3[0].addr();
    let addr_1 = l3[1].addr();
    l3[510].set_addr(addr_0, pt_flags);
    l3[511].set_addr(addr_1, pt_flags);

    // Point L4 at L3
    l4[0].set_addr(phys_addr(l3), pt_flags);
    l4[511].set_addr(phys_addr(l3), pt_flags);

    // Point Cr3 at L4
    let (cr3_frame, cr3_flags) = Cr3::read();
    let l4_frame = PhysFrame::from_start_address(phys_addr(l4)).unwrap();
    if cr3_frame != l4_frame {
        unsafe { Cr3::write(l4_frame, cr3_flags) };
    }
    log::info!("Page tables setup");
}

// Map a virtual address to a PhysAddr (assumes identity mapping)
fn phys_addr<T>(virt_addr: *const T) -> PhysAddr {
    PhysAddr::new(virt_addr as u64)
}
