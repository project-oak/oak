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

use crate::{acpi::AcpiDevice, mm::Translator, ADDRESS_TRANSLATOR, GUEST_HOST_HEAP};
use alloc::vec::Vec;
use anyhow::anyhow;
use core::{
    alloc::{Allocator, Layout},
    ptr::NonNull,
};
use log::info;
use oak_channel::{Read, Write};
use rust_hypervisor_firmware_virtio::pci::VirtioPciTransport;
use spinning_top::Spinlock;
use virtio_drivers::{Hal, MmioTransport, VirtIOConsole};
use x86_64::{PhysAddr, VirtAddr};

pub struct OakHal;

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

// The virtio vsock port on which to listen.
#[cfg(feature = "vsock_channel")]
const VSOCK_PORT: u32 = 1024;

pub struct Channel<T> {
    inner: T,
}

impl<T> Read for Channel<T>
where
    T: oak_virtio::Read,
{
    fn read(&mut self, data: &mut [u8]) -> anyhow::Result<()> {
        self.inner.read(data)
    }
}

impl<T> Write for Channel<T>
where
    T: oak_virtio::Write,
{
    fn write(&mut self, data: &[u8]) -> anyhow::Result<()> {
        self.inner.write(data)
    }
    fn flush(&mut self) -> anyhow::Result<()> {
        self.inner.flush()
    }
}

#[repr(transparent)]
pub struct MmioConsoleChannel<'a> {
    inner: Spinlock<VirtIOConsole<'a, OakHal, MmioTransport>>,
}

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

#[cfg(feature = "virtio_console_channel")]
pub fn get_console_channel<'a, X: Translator>(
    translator: &X,
    devices: Vec<AcpiDevice>,
) -> Channel<MmioConsoleChannel<'a>> {
    use virtio_drivers::{DeviceType, Transport};

    for device in devices {
        let header = translator
            .translate_physical(device.fixed_memory_locations[0].0)
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
                    VirtIOConsole::<OakHal, _>::new(transport).expect("Error initializing console"),
                ),
            },
        };
    }
    panic!("No virtio console devices found");
}

#[cfg(feature = "vsock_channel")]
pub fn get_vsock_channel<'a, X: Translator, A: Allocator>(
    translator: &X,
    alloc: &'a A,
) -> Channel<oak_virtio::vsock::socket::Socket<'a, VirtioPciTransport, A>> {
    let vsock = oak_virtio::vsock::VSock::find_and_configure_device(
        |vaddr: VirtAddr| translator.translate_virtual(vaddr),
        |paddr: PhysAddr| translator.translate_physical(paddr),
        alloc,
    )
    .expect("couldn't configure PCI virtio vsock device");
    info!("Socket device status: {}", vsock.get_status());
    let listener = oak_virtio::vsock::socket::SocketListener::new(vsock, VSOCK_PORT);
    Channel {
        inner: listener.accept().expect("couldn't accept connection"),
    }
}
