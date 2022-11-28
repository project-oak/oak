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

use crate::{
    acpi::{Acpi, AcpiDevice, VIRTIO_MMIO},
    mm::Translator,
    virtio::Channel,
    ADDRESS_TRANSLATOR, GUEST_HOST_HEAP,
};
use alloc::{string::String, vec::Vec};
use aml::{
    resource::{MemoryRangeDescriptor, Resource},
    AmlContext,
};
use anyhow::anyhow;
use core::{
    alloc::{Allocator, Layout},
    ptr::NonNull,
};
use log::info;
use spinning_top::Spinlock;
use virtio_drivers::{DeviceType, Hal, MmioTransport, Transport, VirtIOConsole};
use x86_64::{PhysAddr, VirtAddr};

struct OakHal;

impl Hal for OakHal {
    fn dma_alloc(pages: usize) -> virtio_drivers::PhysAddr {
        // virtio_drivers::PAGE_SIZE is private right now, this has been fixed but not in the latest
        // release
        let vaddr = VirtAddr::from_ptr(
            GUEST_HOST_HEAP
                .get()
                .unwrap()
                .allocate(Layout::from_size_align(pages * 0x1000, 0x1000).unwrap())
                .expect("Failed to allocate memory for virtio MMIO")
                .cast::<u8>()
                .as_ptr(),
        );
        ADDRESS_TRANSLATOR
            .get()
            .unwrap()
            .translate_virtual(vaddr)
            .unwrap()
            .as_u64() as usize
    }

    fn dma_dealloc(paddr: virtio_drivers::PhysAddr, pages: usize) -> i32 {
        let vaddr = ADDRESS_TRANSLATOR
            .get()
            .unwrap()
            .translate_physical(PhysAddr::new(paddr as u64))
            .unwrap();
        unsafe {
            GUEST_HOST_HEAP.get().unwrap().deallocate(
                NonNull::new(vaddr.as_mut_ptr()).unwrap(),
                Layout::from_size_align(pages * 0x1000, 0x1000).unwrap(),
            );
        }

        0
    }

    fn phys_to_virt(paddr: virtio_drivers::PhysAddr) -> virtio_drivers::VirtAddr {
        ADDRESS_TRANSLATOR
            .get()
            .unwrap()
            .translate_physical(PhysAddr::new(paddr as u64))
            .unwrap()
            .as_u64() as usize
    }

    fn virt_to_phys(vaddr: virtio_drivers::VirtAddr) -> virtio_drivers::PhysAddr {
        ADDRESS_TRANSLATOR
            .get()
            .unwrap()
            .translate_virtual(VirtAddr::new(vaddr as u64))
            .unwrap()
            .as_u64() as usize
    }
}

#[repr(transparent)]
pub struct MmioConsoleChannel<'a> {
    inner: Spinlock<VirtIOConsole<'a, OakHal, MmioTransport>>,
}

// Safety: for now, this is safe as we don't have threads in our kernel.
unsafe impl Sync for MmioConsoleChannel<'_> {}
unsafe impl Send for MmioConsoleChannel<'_> {}

impl oak_virtio::Read for MmioConsoleChannel<'_> {
    fn read(&mut self, data: &mut [u8]) -> anyhow::Result<()> {
        let mut console = self.inner.lock();

        let len = data.len();
        let mut count = 0;
        while count < len {
            if let Some(char) = console
                .recv(true)
                .map_err(|err| anyhow!("Virtio console read error: {:?}", err))?
            {
                data[count] = char;
                count = count + 1;
            } else {
                // If we didn't have any data to read, try acking any pending interrupts. We don't
                // have general support for interrupts yet, so we need to do it blindly here.
                console.ack_interrupt().unwrap();
            }
        }

        Ok(())
    }
}

impl oak_virtio::Write for MmioConsoleChannel<'_> {
    fn write(&mut self, data: &[u8]) -> anyhow::Result<()> {
        let mut console = self.inner.lock();

        for char in data {
            console
                .send(*char)
                .map_err(|err| anyhow!("Virtio console write error: {:?}", err))?;
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
                ))
            }
            _ => continue,
        }
    }
    None
}

pub fn get_console_channel<'a>(
    translator: &impl Translator,
    acpi: &mut Acpi,
) -> Channel<MmioConsoleChannel<'a>> {
    let devices = acpi.devices().unwrap();

    let virtio_devices: Vec<&AcpiDevice> = devices
        .iter()
        .filter(|device| {
            device.hid(&mut acpi.aml).ok().flatten() == Some(String::from(VIRTIO_MMIO))
        })
        .collect();

    for device in virtio_devices {
        let header = translator
            .translate_physical(
                find_memory_range(device, &mut acpi.aml)
                    .expect("unable to determine physical memory range for virtio MMIO device")
                    .0,
            )
            .unwrap();

        let transport =
            unsafe { MmioTransport::new(core::ptr::NonNull::new(header.as_mut_ptr()).unwrap()) }
                .expect("MMIO transport setup error");

        if transport.device_type() != DeviceType::Console {
            continue;
        }

        info!(
            "Using virtio console over MMIO; ACPI device name {}, vendor ID: {:x}",
            device.name,
            transport.vendor_id()
        );
        return Channel {
            inner: MmioConsoleChannel {
                inner: Spinlock::new(
                    VirtIOConsole::<OakHal, _>::new(transport).expect("error initializing console"),
                ),
            },
        };
    }
    panic!("No virtio console devices found");
}
