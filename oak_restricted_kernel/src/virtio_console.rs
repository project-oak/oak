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

use alloc::{string::String, vec::Vec};
use core::{
    alloc::{Allocator, Layout},
    ptr::NonNull,
};

use aml::{
    resource::{MemoryRangeDescriptor, Resource},
    AmlContext,
};
use anyhow::anyhow;
use log::info;
use spinning_top::Spinlock;
use virtio_drivers::{
    device::console::VirtIOConsole,
    transport::{mmio::MmioTransport, DeviceType, Transport},
    BufferDirection, Hal, PAGE_SIZE,
};
use x86_64::{PhysAddr, VirtAddr};

use crate::{
    acpi::{Acpi, AcpiDevice, VIRTIO_MMIO},
    mm::Translator,
    GUEST_HOST_HEAP, PAGE_TABLES,
};

struct OakHal;

unsafe impl Hal for OakHal {
    fn dma_alloc(
        pages: usize,
        _direction: BufferDirection,
    ) -> (virtio_drivers::PhysAddr, NonNull<u8>) {
        let vaddr = GUEST_HOST_HEAP
            .get()
            .unwrap()
            .allocate(Layout::from_size_align(pages * PAGE_SIZE, PAGE_SIZE).unwrap())
            .expect("Failed to allocate memory for virtio MMIO")
            .cast::<u8>();
        let phys_addr = PAGE_TABLES
            .lock()
            .get()
            .unwrap()
            .translate_virtual(VirtAddr::from_ptr(vaddr.as_ptr()))
            .unwrap()
            .as_u64();
        (phys_addr, vaddr)
    }

    unsafe fn dma_dealloc(
        paddr: virtio_drivers::PhysAddr,
        vaddr: NonNull<u8>,
        pages: usize,
    ) -> i32 {
        let vaddr_check = Self::mmio_phys_to_virt(paddr, 0);
        assert_eq!(vaddr_check, vaddr, "dma buffer physical and virtual addresses don't match",);
        GUEST_HOST_HEAP
            .get()
            .unwrap()
            .deallocate(vaddr, Layout::from_size_align(pages * PAGE_SIZE, PAGE_SIZE).unwrap());

        0
    }

    unsafe fn mmio_phys_to_virt(paddr: virtio_drivers::PhysAddr, _size: usize) -> NonNull<u8> {
        NonNull::new(
            PAGE_TABLES
                .lock()
                .get()
                .unwrap()
                .translate_physical(PhysAddr::new(paddr))
                .unwrap()
                .as_mut_ptr(),
        )
        .unwrap()
    }

    unsafe fn share(
        buffer: NonNull<[u8]>,
        _direction: BufferDirection,
    ) -> virtio_drivers::PhysAddr {
        // No additional work needed for sharing as the buffer was allocated from the
        // guest-host allocator.
        PAGE_TABLES
            .lock()
            .get()
            .unwrap()
            .translate_virtual(VirtAddr::from_ptr(buffer.cast::<u8>().as_ptr()))
            .unwrap()
            .as_u64()
    }

    unsafe fn unshare(
        _paddr: virtio_drivers::PhysAddr,
        _buffer: NonNull<[u8]>,
        _direction: BufferDirection,
    ) {
        // No additional work needed for unsharing as the buffer was allocated
        // from the guest-host allocator.
    }
}

#[repr(transparent)]
pub struct MmioConsoleChannel<'a> {
    inner: Spinlock<VirtIOConsole<OakHal, MmioTransport<'a>>>,
}

// Safety: for now, this is safe as we don't have threads in our kernel.
// TODO(#3531): this will most likely break once we do add threads, though.
unsafe impl Sync for MmioConsoleChannel<'_> {}
unsafe impl Send for MmioConsoleChannel<'_> {}

impl oak_channel::Read for MmioConsoleChannel<'_> {
    fn read_exact(&mut self, data: &mut [u8]) -> anyhow::Result<()> {
        let mut console = self.inner.lock();

        let len = data.len();
        let mut count = 0;
        while count < len {
            if let Some(char) =
                console.recv(true).map_err(|err| anyhow!("Virtio console read error: {:?}", err))?
            {
                data[count] = char;
                count += 1;
            }
        }

        Ok(())
    }
}

impl oak_channel::Write for MmioConsoleChannel<'_> {
    fn write_all(&mut self, data: &[u8]) -> anyhow::Result<()> {
        let mut console = self.inner.lock();

        for char in data {
            console.send(*char).map_err(|err| anyhow!("Virtio console write error: {:?}", err))?;
        }

        Ok(())
    }

    fn flush(&mut self) -> anyhow::Result<()> {
        Ok(())
    }
}

fn find_memory_range(device: &AcpiDevice, ctx: &mut AmlContext) -> Option<(PhysAddr, PhysAddr)> {
    for resource in device.crs(ctx).unwrap().unwrap() {
        match resource {
            Resource::MemoryRange(MemoryRangeDescriptor::FixedLocation {
                is_writable: _,
                base_address,
                range_length,
            }) => {
                return Some((
                    PhysAddr::new(base_address as u64),
                    PhysAddr::new((base_address + range_length) as u64),
                ));
            }
            _ => continue,
        }
    }
    None
}

pub fn get_console_channel<'a>(acpi: &mut Acpi) -> MmioConsoleChannel<'a> {
    let devices = acpi.devices().unwrap();

    let virtio_devices: Vec<&AcpiDevice> = devices
        .iter()
        .filter(|device| {
            device.hid(&mut acpi.aml).ok().flatten() == Some(String::from(VIRTIO_MMIO))
        })
        .collect();

    for device in virtio_devices {
        let acpi_aml_range = find_memory_range(device, &mut acpi.aml)
            .expect("unable to determine physical memory range for virtio MMIO device");

        let header =
            PAGE_TABLES.lock().get().unwrap().translate_physical(acpi_aml_range.0).unwrap();

        let mmio_size = acpi_aml_range.1 - acpi_aml_range.0;

        info!(
            "Found virtio MMIO device {}; physical range: 0x{:x} - 0x{:x}, size: 0x{:x}",
            device.name, acpi_aml_range.0, acpi_aml_range.1, mmio_size
        );

        let transport = unsafe {
            MmioTransport::new(
                core::ptr::NonNull::new(header.as_mut_ptr()).unwrap(),
                mmio_size as usize,
            )
        }
        .expect("MMIO transport setup error");

        if transport.device_type() != DeviceType::Console {
            continue;
        }

        info!(
            "Using virtio console over MMIO; ACPI device name {}, vendor ID: {:x}",
            device.name,
            transport.vendor_id()
        );
        return MmioConsoleChannel {
            inner: Spinlock::new(
                VirtIOConsole::<OakHal, _>::new(transport).expect("error initializing console"),
            ),
        };
    }
    panic!("No virtio console devices found");
}
