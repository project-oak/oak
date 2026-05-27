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
    mem::size_of,
    ptr::NonNull,
};

use aml::{
    AmlContext,
    resource::{MemoryRangeDescriptor, Resource},
};
use anyhow::anyhow;
use bitflags::bitflags;
use log::info;
use oak_hal::{Mmio, Platform};
use spinning_top::Spinlock;
use virtio_drivers::{
    BufferDirection, Hal, PAGE_SIZE,
    queue::VirtQueue,
    transport::{DeviceStatus, DeviceType, InterruptStatus, Transport},
};
use x86_64::{PhysAddr, VirtAddr};
use zerocopy::{FromBytes, Immutable, IntoBytes};

use crate::{
    GUEST_HOST_HEAP, PAGE_TABLES,
    acpi::{Acpi, AcpiDevice, VIRTIO_MMIO},
    mm::Translator,
    virtio_console::reg::CONFIG_SPACE,
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
        let negotiated_features = transport
            .begin_init(ConsoleFeatures::VERSION_1.union(ConsoleFeatures::ACCESS_PLATFORM));
        assert!(
            negotiated_features.contains(ConsoleFeatures::VERSION_1),
            "legacy virtio not supported"
        );
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

// VirtIO MMIO register offsets, expressed as u32 indices (byte offset / 4).
//
// See <https://docs.oasis-open.org/virtio/virtio/v1.2/cs01/virtio-v1.2-cs01.html#x1-1460002>.
mod reg {
    /// Magic value; must read 0x74726976 ("virt").
    #[allow(clippy::erasing_op)]
    pub const MAGIC: usize = 0x000 / size_of::<u32>();
    /// Device version number (1 = legacy, 2 = modern).
    pub const VERSION: usize = 0x004 / size_of::<u32>();
    /// Virtio subsystem device ID.
    pub const DEVICE_ID: usize = 0x008 / size_of::<u32>();
    /// Virtio subsystem vendor ID.
    pub const VENDOR_ID: usize = 0x00C / size_of::<u32>();
    /// Flags representing features the device supports.
    pub const DEVICE_FEATURES: usize = 0x010 / size_of::<u32>();
    /// Device (host) features word selection.
    pub const DEVICE_FEATURES_SEL: usize = 0x014 / size_of::<u32>();
    /// Flags representing device features understood and activated by the
    /// driver.
    pub const DRIVER_FEATURES: usize = 0x020 / size_of::<u32>();
    /// Activated (guest) features word selection.
    pub const DRIVER_FEATURES_SEL: usize = 0x024 / size_of::<u32>();
    /// Virtual queue index selection.
    pub const QUEUE_SEL: usize = 0x030 / size_of::<u32>();
    /// Maximum virtual queue size.
    pub const QUEUE_NUM_MAX: usize = 0x034 / size_of::<u32>();
    /// Virtual queue size.
    pub const QUEUE_NUM: usize = 0x038 / size_of::<u32>();
    /// Queue ready flag (modern interface).
    pub const QUEUE_READY: usize = 0x044 / size_of::<u32>();
    /// Queue notifier.
    pub const QUEUE_NOTIFY: usize = 0x050 / size_of::<u32>();
    /// Interrupt status.
    pub const INTERRUPT_STATUS: usize = 0x060 / size_of::<u32>();
    /// Interrupt acknowledge.
    pub const INTERRUPT_ACK: usize = 0x064 / size_of::<u32>();
    /// Device status.
    pub const STATUS: usize = 0x070 / size_of::<u32>();
    /// Queue descriptor table address (low 32 bits, modern).
    pub const QUEUE_DESC_LOW: usize = 0x080 / size_of::<u32>();
    /// Queue descriptor table address (high 32 bits, modern).
    pub const QUEUE_DESC_HIGH: usize = 0x084 / size_of::<u32>();
    /// Queue available ring address (low 32 bits, modern).
    pub const QUEUE_DRIVER_LOW: usize = 0x090 / size_of::<u32>();
    /// Queue available ring address (high 32 bits, modern).
    pub const QUEUE_DRIVER_HIGH: usize = 0x094 / size_of::<u32>();
    /// Queue used ring address (low 32 bits, modern).
    pub const QUEUE_DEVICE_LOW: usize = 0x0A0 / size_of::<u32>();
    /// Queue used ring address (high 32 bits, modern).
    pub const QUEUE_DEVICE_HIGH: usize = 0x0A4 / size_of::<u32>();
    /// Configuration atomicity value.
    pub const CONFIG_GENERATION: usize = 0x0FC / size_of::<u32>();
    /// Start of the device-specific configuration space.
    pub const CONFIG_SPACE: usize = 0x100 / size_of::<u32>();
}

/// Expected magic value in the VirtIO MMIO header.
const VIRTIO_MAGIC: u32 = 0x7472_6976;
/// Modern VirtIO MMIO version.
const MODERN_VERSION: u32 = 2;

/// An MMIO-based VirtIO transport that delegates all MMIO access through the
/// [`oak_hal::Mmio`] trait.
///
/// This allows the transport to work transparently on platforms where MMIO
/// access cannot be performed via direct volatile reads/writes (e.g. SEV-ES
/// and above, where MMIO must go through the GHCB).
///
/// Only the modern (v2) VirtIO MMIO interface is supported.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.2/cs01/virtio-v1.2-cs01.html#x1-1460002>.
struct OakMmioTransport<M: Mmio> {
    mmio: M,
    /// Cached device type, read during construction.
    device_type: DeviceType,
}

impl<M: Mmio> OakMmioTransport<M> {
    /// Creates a new `OakMmioTransport` by validating the VirtIO MMIO header.
    ///
    /// # Arguments
    ///
    /// * `mmio` - An implementation of the `oak_hal::Mmio` trait pointing at
    ///   the VirtIO MMIO region.
    /// * `region_size` - The total size of the MMIO region in bytes.
    ///
    /// # Errors
    ///
    /// Returns an error if the magic value is wrong, the version is not modern
    /// (v2), the device ID is invalid, or the region size is too small.
    fn new(mmio: M) -> anyhow::Result<Self> {
        anyhow::ensure!(
            mmio.region_size() >= CONFIG_SPACE * size_of::<u32>(),
            "MMIO region size is too small"
        );
        let magic = mmio.read_u32(reg::MAGIC);
        anyhow::ensure!(
            magic == VIRTIO_MAGIC,
            "invalid VirtIO MMIO magic value {magic:#010x} (expected {VIRTIO_MAGIC:#010x})"
        );

        let version = mmio.read_u32(reg::VERSION);
        anyhow::ensure!(
            version == MODERN_VERSION,
            "unsupported VirtIO MMIO version {version} (only modern v2 is supported)"
        );

        let device_id = mmio.read_u32(reg::DEVICE_ID);
        let device_type = DeviceType::try_from(device_id as u8)
            .map_err(|e| anyhow!("invalid VirtIO device ID {device_id}: {e}"))?;

        Ok(Self { mmio, device_type })
    }

    /// Returns the vendor ID reported by the device.
    fn vendor_id(&self) -> u32 {
        self.mmio.read_u32(reg::VENDOR_ID)
    }
}

impl<M: Mmio> Transport for OakMmioTransport<M> {
    fn device_type(&self) -> DeviceType {
        self.device_type
    }

    fn read_device_features(&mut self) -> u64 {
        // Select and read the low 32 bits.
        // Safety: writing the feature selection register is always valid.
        unsafe { self.mmio.write_u32(reg::DEVICE_FEATURES_SEL, 0) };
        let low = self.mmio.read_u32(reg::DEVICE_FEATURES);

        // Select and read the high 32 bits.
        // Safety: writing the feature selection register is always valid.
        unsafe { self.mmio.write_u32(reg::DEVICE_FEATURES_SEL, 1) };
        let high = self.mmio.read_u32(reg::DEVICE_FEATURES);

        (high as u64) << 32 | low as u64
    }

    fn write_driver_features(&mut self, driver_features: u64) {
        // Safety: writing the feature registers is valid during initialization.
        unsafe {
            // Write low 32 bits.
            self.mmio.write_u32(reg::DRIVER_FEATURES_SEL, 0);
            self.mmio.write_u32(reg::DRIVER_FEATURES, driver_features as u32);

            // Write high 32 bits.
            self.mmio.write_u32(reg::DRIVER_FEATURES_SEL, 1);
            self.mmio.write_u32(reg::DRIVER_FEATURES, (driver_features >> 32) as u32);
        }
    }

    fn max_queue_size(&mut self, queue: u16) -> u32 {
        // Safety: selecting a queue is always valid.
        unsafe { self.mmio.write_u32(reg::QUEUE_SEL, queue as u32) };
        self.mmio.read_u32(reg::QUEUE_NUM_MAX)
    }

    fn notify(&mut self, queue: u16) {
        // Safety: notifying a queue is always valid.
        unsafe { self.mmio.write_u32(reg::QUEUE_NOTIFY, queue as u32) };
    }

    fn get_status(&self) -> DeviceStatus {
        let bits = self.mmio.read_u32(reg::STATUS);
        DeviceStatus::from_bits_retain(bits)
    }

    fn set_status(&mut self, status: DeviceStatus) {
        // Safety: writing the status register is valid during
        // initialization/reset.
        unsafe { self.mmio.write_u32(reg::STATUS, status.bits()) };
    }

    fn set_guest_page_size(&mut self, _guest_page_size: u32) {
        // No-op for the modern (v2) interface.
    }

    fn requires_legacy_layout(&self) -> bool {
        // Even though we don't support legacy mode it seems QEMU doesn't like the
        // flexible virtqueue layout even when legacy mode is disabled.
        true
    }

    fn queue_set(
        &mut self,
        queue: u16,
        size: u32,
        descriptors: virtio_drivers::PhysAddr,
        driver_area: virtio_drivers::PhysAddr,
        device_area: virtio_drivers::PhysAddr,
    ) {
        // Safety: all queue configuration register writes are valid.
        unsafe {
            self.mmio.write_u32(reg::QUEUE_SEL, queue as u32);
            self.mmio.write_u32(reg::QUEUE_NUM, size);

            self.mmio.write_u32(reg::QUEUE_DESC_LOW, descriptors as u32);
            self.mmio.write_u32(reg::QUEUE_DESC_HIGH, (descriptors >> 32) as u32);

            self.mmio.write_u32(reg::QUEUE_DRIVER_LOW, driver_area as u32);
            self.mmio.write_u32(reg::QUEUE_DRIVER_HIGH, (driver_area >> 32) as u32);

            self.mmio.write_u32(reg::QUEUE_DEVICE_LOW, device_area as u32);
            self.mmio.write_u32(reg::QUEUE_DEVICE_HIGH, (device_area >> 32) as u32);

            // Mark the queue as ready.
            self.mmio.write_u32(reg::QUEUE_READY, 1);
        }
    }

    fn queue_unset(&mut self, queue: u16) {
        // Safety: queue configuration register writes are always valid.
        unsafe {
            self.mmio.write_u32(reg::QUEUE_SEL, queue as u32);
            self.mmio.write_u32(reg::QUEUE_READY, 0);
            self.mmio.write_u32(reg::QUEUE_NUM, 0);

            self.mmio.write_u32(reg::QUEUE_DESC_LOW, 0);
            self.mmio.write_u32(reg::QUEUE_DESC_HIGH, 0);
            self.mmio.write_u32(reg::QUEUE_DRIVER_LOW, 0);
            self.mmio.write_u32(reg::QUEUE_DRIVER_HIGH, 0);
            self.mmio.write_u32(reg::QUEUE_DEVICE_LOW, 0);
            self.mmio.write_u32(reg::QUEUE_DEVICE_HIGH, 0);
        }
    }

    fn queue_used(&mut self, queue: u16) -> bool {
        // Safety: selecting a queue is always valid.
        unsafe { self.mmio.write_u32(reg::QUEUE_SEL, queue as u32) };
        self.mmio.read_u32(reg::QUEUE_READY) != 0
    }

    fn ack_interrupt(&mut self) -> InterruptStatus {
        let status = self.mmio.read_u32(reg::INTERRUPT_STATUS);
        // Safety: acknowledging an interrupt is always valid.
        unsafe { self.mmio.write_u32(reg::INTERRUPT_ACK, status) };
        InterruptStatus::from_bits_retain(status)
    }

    fn read_config_generation(&self) -> u32 {
        self.mmio.read_u32(reg::CONFIG_GENERATION)
    }

    fn read_config_space<T: FromBytes + IntoBytes>(
        &self,
        _offset: usize,
    ) -> virtio_drivers::Result<T> {
        // We don't need to support config space access for our simple console
        // implementation since we don't support a sized console.
        Err(virtio_drivers::Error::Unsupported)
    }

    fn write_config_space<T: IntoBytes + Immutable>(
        &mut self,
        _offset: usize,
        _value: T,
    ) -> virtio_drivers::Result<()> {
        // We don't need to support config space access for our simple console
        // implementation since we don't support a sized console.
        Err(virtio_drivers::Error::Unsupported)
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
pub struct MmioConsoleChannel<'a, A: Allocator, P: Platform> {
    inner: Spinlock<Console<'a, OakHal, OakMmioTransport<P::Mmio>, A>>,
}

// Safety: for now, this is safe as we don't have threads in our kernel.
// TODO(#3531): this will most likely break once we do add threads, though.
unsafe impl<A: Allocator, P: Platform> Sync for MmioConsoleChannel<'_, A, P> {}
unsafe impl<A: Allocator, P: Platform> Send for MmioConsoleChannel<'_, A, P> {}

impl<A: Allocator, P: Platform> oak_channel::Read for MmioConsoleChannel<'_, A, P> {
    fn read_exact(&mut self, data: &mut [u8]) -> anyhow::Result<()> {
        let mut console = self.inner.lock();
        console.read_exact(data).map_err(|err| {
            anyhow!("Virtio console read_exact error: {:?}, requested length: {}", err, data.len())
        })
    }
}

impl<A: Allocator, P: Platform> oak_channel::Write for MmioConsoleChannel<'_, A, P> {
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

pub fn get_console_channel<'a, A: Allocator, P: Platform>(
    acpi: &mut Acpi,
    alloc: &'a A,
) -> MmioConsoleChannel<'a, A, P> {
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

        let mmio_size = acpi_aml_range.1 - acpi_aml_range.0;

        info!(
            "Found virtio MMIO device {}; physical range: 0x{:x} - 0x{:x}, size: 0x{:x}",
            device.name, acpi_aml_range.0, acpi_aml_range.1, mmio_size
        );

        // Safety: the ACPI tables describe a valid MMIO region.
        let mmio = unsafe { P::mmio(acpi_aml_range.0, mmio_size as usize) };

        let transport = OakMmioTransport::new(mmio).expect("MMIO transport setup error");

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
