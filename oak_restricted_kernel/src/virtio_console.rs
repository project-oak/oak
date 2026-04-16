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

use alloc::{boxed::Box, collections::VecDeque, string::String, vec::Vec};
use core::{
    alloc::{Allocator, Layout},
    ptr::NonNull,
};

use aml::{
    AmlContext,
    resource::{MemoryRangeDescriptor, Resource},
};
use anyhow::anyhow;
use bitflags::bitflags;
use log::info;
use spinning_top::Spinlock;
use virtio_drivers::{
    BufferDirection, Hal, PAGE_SIZE,
    queue::VirtQueue,
    transport::{DeviceType, Transport, mmio::MmioTransport},
};
use x86_64::{PhysAddr, VirtAddr};

use crate::{
    GUEST_HOST_HEAP, PAGE_TABLES,
    acpi::{Acpi, AcpiDevice, VIRTIO_MMIO},
    mm::Translator,
};

/// The number of buffer descriptors in each of the queues. For now we only
/// support one buffer for each queue.
const QUEUE_SIZE: usize = 1;
/// The id of the receive queue.
const RX_QUEUE_ID: u16 = 0;
/// The id of the transmit queue.
const TX_QUEUE_ID: u16 = 1;

bitflags! {
    /// Minimal features needed for the console device.
    #[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
    struct ConsoleFeatures: u64 {
        const VERSION_1             = 1 << 32;
        const ACCESS_PLATFORM       = 1 << 33;
    }
}

/// Simple driver implementation for a virtio-console device that only supports
/// a single port and no configuration.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-39000010>.
struct Console<'a, H: Hal, T: Transport, A: Allocator> {
    /// The transport for configuring the device.
    transport: T,
    /// The virtqueue for receiving bytes.
    rx_queue: VirtQueue<H, QUEUE_SIZE>,
    /// The virtqueue for transmitting bytes.
    tx_queue: VirtQueue<H, QUEUE_SIZE>,
    /// A single read buffer.
    rx_buffer: Box<[u8; PAGE_SIZE], &'a A>,
    /// Token for the receive queue.
    rx_token: u16,
    /// A single write buffer.
    tx_buffer: Box<[u8; PAGE_SIZE], &'a A>,
    /// Data that has been received from the queue but not yet read.
    pending_data: Option<VecDeque<u8>>,
}

impl<'a, H: Hal, T: Transport, A: Allocator> Console<'a, H, T, A> {
    fn new(mut transport: T, alloc: &'a A) -> anyhow::Result<Self> {
        transport.begin_init(ConsoleFeatures::VERSION_1.union(ConsoleFeatures::ACCESS_PLATFORM));
        let mut rx_queue = VirtQueue::new(&mut transport, RX_QUEUE_ID, false, false)?;
        let tx_queue = VirtQueue::new(&mut transport, TX_QUEUE_ID, false, false)?;

        transport.finish_init();

        let mut rx_buffer = Box::new_in([0; PAGE_SIZE], alloc);
        let tx_buffer = Box::new_in([0; PAGE_SIZE], alloc);

        // Set the receive buffer to be ready to receive messages.
        //
        // SAFETY: the buffer lives as long as the queue and there are no pending
        // requests in the queue.
        let rx_token = unsafe { rx_queue.add(&[], &mut [rx_buffer.as_mut().as_mut_slice()]) }?;
        if rx_queue.should_notify() {
            transport.notify(RX_QUEUE_ID);
        }

        Ok(Self {
            transport,
            rx_queue,
            tx_queue,
            rx_buffer,
            rx_token,
            tx_buffer,
            pending_data: None,
        })
    }

    /// Reads the next available bytes from the receive queue, if any are
    /// available.
    fn read_bytes(&mut self) -> Option<VecDeque<u8>> {
        // Read the buffer if it has been used.
        if self.rx_token == self.rx_queue.peek_used()? {
            // SAFETY: This is the same buffer that was used when calling `add` and it has
            // now been used.
            let len = unsafe {
                self.rx_queue
                    .pop_used(self.rx_token, &[], &mut [self.rx_buffer.as_mut_slice()])
                    .expect("receive queue is misconfigured")
            } as usize;
            assert!(len <= self.rx_buffer.len());
            let mut result = VecDeque::with_capacity(len);
            result.extend(&self.rx_buffer[..len]);

            // Reset the receive buffer to be ready for the next message.
            //
            // SAFETY: the buffer lives as long as the queue and there are no pending
            // requests in the queue.
            self.rx_token =
                unsafe { self.rx_queue.add(&[], &mut [self.rx_buffer.as_mut().as_mut_slice()]) }
                    .expect("receive queue is misconfigured");
            if self.rx_queue.should_notify() {
                self.transport.notify(RX_QUEUE_ID);
            }
            Some(result)
        } else {
            panic!("receive queue is misconfigured");
        }
    }

    /// Writes the data to the transmit queue.
    ///
    /// Returns the number of bytes written, if any.
    fn write_bytes(&mut self, data: &[u8]) -> anyhow::Result<usize> {
        if data.is_empty() {
            return Ok(0);
        }

        // We have to copy the data into the shared write buffer.
        let len = data.len().min(self.tx_buffer.len());
        self.tx_buffer.as_mut()[..len].copy_from_slice(&data[..len]);
        self.tx_queue.add_notify_wait_pop(
            &[&self.tx_buffer[..len]],
            &mut [],
            &mut self.transport,
        )?;
        Ok(len)
    }

    /// Tries once to fill the destination with as much data as is currently
    /// available, either in the pending buffer (if data was left over from
    /// the previous read), or from the next available buffer in the queue
    /// if there was no data in the pending buffer.
    ///
    /// If data is read from the queue and not fully used the remainder is
    /// stored back into the pending buffer.
    ///
    /// Returns the number of bytes read if any data was available to read.
    fn read_partial(&mut self, dest: &mut [u8]) -> Option<usize> {
        let mut source = match self.pending_data.take() {
            Some(data) => data,
            None => self.read_bytes()?,
        };
        let len = dest.len();
        let mut position = 0;
        while position < len
            && let Some(byte) = source.pop_front()
        {
            dest[position] = byte;
            position += 1;
        }
        if !source.is_empty() {
            self.pending_data.replace(source);
        }
        Some(position)
    }
}

impl<H: Hal, T: Transport, A: Allocator> oak_channel::Read for Console<'_, H, T, A> {
    fn read_exact(&mut self, data: &mut [u8]) -> anyhow::Result<()> {
        let len = data.len();
        let mut count = 0;
        while count < len {
            count += self.read_partial(&mut data[count..]).unwrap_or(0);
        }
        Ok(())
    }
}

impl<H: Hal, T: Transport, A: Allocator> oak_channel::Write for Console<'_, H, T, A> {
    fn write_all(&mut self, data: &[u8]) -> anyhow::Result<()> {
        let mut start = 0;
        let data_len = data.len();
        while start < data_len {
            let count = self.write_bytes(&data[start..])?;
            start += count;
        }
        Ok(())
    }
    fn flush(&mut self) -> anyhow::Result<()> {
        // We always flush on write, so do nothing.
        Ok(())
    }
}

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
        let vaddr_check = unsafe { Self::mmio_phys_to_virt(paddr, 0) };
        assert_eq!(vaddr_check, vaddr, "dma buffer physical and virtual addresses don't match",);
        unsafe {
            GUEST_HOST_HEAP
                .get()
                .unwrap()
                .deallocate(vaddr, Layout::from_size_align(pages * PAGE_SIZE, PAGE_SIZE).unwrap());
        }

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
pub struct MmioConsoleChannel<'a, A: Allocator> {
    inner: Spinlock<Console<'a, OakHal, MmioTransport<'a>, A>>,
}

// Safety: for now, this is safe as we don't have threads in our kernel.
// TODO(#3531): this will most likely break once we do add threads, though.
unsafe impl<A: Allocator> Sync for MmioConsoleChannel<'_, A> {}
unsafe impl<A: Allocator> Send for MmioConsoleChannel<'_, A> {}

impl<A: Allocator> oak_channel::Read for MmioConsoleChannel<'_, A> {
    fn read_exact(&mut self, data: &mut [u8]) -> anyhow::Result<()> {
        let mut console = self.inner.lock();
        console.read_exact(data).map_err(|err| {
            anyhow!("Virtio console read_exact error: {:?}, requested length: {}", err, data.len())
        })
    }
}

impl<A: Allocator> oak_channel::Write for MmioConsoleChannel<'_, A> {
    fn write_all(&mut self, data: &[u8]) -> anyhow::Result<()> {
        let mut console = self.inner.lock();

        for chunk in data.chunks(PAGE_SIZE) {
            console
                .write_all(chunk)
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
                ));
            }
            _ => continue,
        }
    }
    None
}

pub fn get_console_channel<'a, A: Allocator>(
    acpi: &mut Acpi,
    alloc: &'a A,
) -> MmioConsoleChannel<'a, A> {
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
                Console::<OakHal, _, _>::new(transport, alloc).expect("error initializing console"),
            ),
        };
    }
    panic!("No virtio console devices found");
}
