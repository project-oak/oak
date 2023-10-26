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

use core::alloc::Allocator;

use crate::{
    queue::{DeviceWriteOnlyQueue, DriverWriteOnlyQueue},
    InverseTranslator, Read, Translator, Write,
};
use alloc::collections::VecDeque;
use anyhow::Context;
use rust_hypervisor_firmware_virtio::{
    device::VirtioBaseDevice,
    pci::{find_device, VirtioPciTransport},
    virtio::VirtioTransport,
};

/// The number of buffer descriptors in each of the queues.
const QUEUE_SIZE: usize = 16;

/// The size of each of the buffers used by the transmit and receive queues.
const DATA_BUFFER_SIZE: usize = 4096;

/// The id of the receive queue.
const RX_QUEUE_ID: u16 = 0;

/// The id of the transmit queue.
const TX_QUEUE_ID: u16 = 1;

/// The virtio device id for a console device.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-2560001>.
const DEVICE_ID: u16 = 3;

/// The PCI device id for a virtio console device.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-1020002>.
const PCI_DEVICE_ID: u16 = 0x1040 + DEVICE_ID;

/// Simple driver implementation for a virtio serial/console device that only supports a single port
/// and no configuration.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-39000010>.
pub struct Console<'a, T: VirtioTransport, A: Allocator> {
    /// The base virtio-over-PCI device used for configuration and notification.
    device: VirtioBaseDevice<T>,
    /// The receive queue, used for receiving bytes.
    rx_queue: DeviceWriteOnlyQueue<'a, QUEUE_SIZE, DATA_BUFFER_SIZE, A>,
    /// The transmit queue, used for sending bytes.
    tx_queue: DriverWriteOnlyQueue<'a, QUEUE_SIZE, DATA_BUFFER_SIZE, A>,
    /// A buffer to temporarily store extra data from the device that was not fully read when using
    /// `read_all`. This could happen if the device sent more bytes in a single buffer than was
    /// expected by `read_all`.
    pending_data: Option<VecDeque<u8>>,
}

impl<'a, A: Allocator> Console<'a, VirtioPciTransport, A> {
    /// Finds the virtio console PCI device, initialises the device, and configures the queues.
    pub fn find_and_configure_device<VP: Translator, PV: InverseTranslator>(
        translate: VP,
        inverse: PV,
        alloc: &'a A,
    ) -> anyhow::Result<Self> {
        // For now we just scan the first 32 devices on PCI bus 0 to find the first one that matches
        // the vendor ID and device ID.
        let pci_device = find_device(super::PCI_VENDOR_ID, PCI_DEVICE_ID)
            .ok_or_else(|| anyhow::anyhow!("couldn't find a virtio console device"))?;
        let transport = VirtioPciTransport::new(pci_device);
        let device = VirtioBaseDevice::new(transport);
        let mut result = Self::new(device, &translate, alloc);
        result.init(translate, inverse)?;
        Ok(result)
    }
}

impl<'a, T, A: Allocator> Console<'a, T, A>
where
    T: VirtioTransport,
{
    /// Reads the next available bytes from the receive queue, if any are available.
    pub fn read_bytes(&mut self) -> Option<VecDeque<u8>> {
        let buffer = self.rx_queue.read_next_used_buffer()?;
        let mut result = VecDeque::with_capacity(buffer.len());
        result.extend(buffer);

        if self.rx_queue.inner.must_notify_device() {
            // Notify the device that bytes have been read and the buffer is available again.
            self.device.notify_queue(RX_QUEUE_ID);
        }

        Some(result)
    }

    /// Writes the data to the transmit queue.
    ///
    /// Returns the number of bytes written, if any.
    pub fn write_bytes(&mut self, data: &[u8]) -> Option<usize> {
        if data.is_empty() {
            return None;
        }

        let result = self.tx_queue.write_buffer(data);

        if self.tx_queue.inner.must_notify_device() {
            // Notify the device that new bytes have been written.
            self.device.notify_queue(TX_QUEUE_ID);
        }

        result
    }

    /// Gets the device status.
    ///
    /// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-100001>.
    pub fn get_status(&self) -> u32 {
        self.device.get_status()
    }

    fn new<VP: Translator>(device: VirtioBaseDevice<T>, translate: VP, alloc: &'a A) -> Self {
        let tx_queue = DriverWriteOnlyQueue::new(&translate, alloc);
        let rx_queue = DeviceWriteOnlyQueue::new(&translate, alloc);
        Console {
            device,
            tx_queue,
            rx_queue,
            pending_data: None,
        }
    }

    /// Initializes the device and configures the queues.
    fn init<VP: Translator, PV: InverseTranslator>(
        &mut self,
        translate: VP,
        inverse: PV,
    ) -> anyhow::Result<()> {
        self.device
            .start_init(DEVICE_ID as u32, inverse)
            .map_err(|error| anyhow::anyhow!("virtio error: {:?}", error))
            .context("couldn't initialize the PCI device")?;
        self.device
            .configure_queue(
                RX_QUEUE_ID,
                QUEUE_SIZE as u16,
                translate(self.rx_queue.inner.get_desc_addr())
                    .context("couldn't translate VirtAddr to PhysAddr")?,
                translate(self.rx_queue.inner.get_avail_addr())
                    .context("couldn't translate VirtAddr to PhysAddr")?,
                translate(self.rx_queue.inner.get_used_addr())
                    .context("couldn't translate VirtAddr to PhysAddr")?,
            )
            .map_err(|error| anyhow::anyhow!("queue configuration error: {:?}", error))
            .context("couldn't configure the receive queue")?;
        self.device
            .configure_queue(
                TX_QUEUE_ID,
                QUEUE_SIZE as u16,
                translate(self.tx_queue.inner.get_desc_addr())
                    .context("couldn't translate VirtAddr to PhysAddr")?,
                translate(self.tx_queue.inner.get_avail_addr())
                    .context("couldn't translate VirtAddr to PhysAddr")?,
                translate(self.tx_queue.inner.get_used_addr())
                    .context("couldn't translate VirtAddr to PhysAddr")?,
            )
            .map_err(|error| anyhow::anyhow!("queue configuration error: {:?}", error))
            .context("couldn't configure the transmit queue")?;
        self.device
            .complete_init()
            .map_err(|error| anyhow::anyhow!("device activation error: {:?}", error))
            .context("couldn't activate the PCI device")?;

        // Let the device know there are available buffers in the receiver queue.
        self.device.notify_queue(RX_QUEUE_ID);

        Ok(())
    }

    /// Tries once to fill the destination with as much data as is currently available, either in
    /// the pending buffer (if data was left over from the previous read), or from the next
    /// available buffer in the queue if there was no data in the pending buffer.
    ///
    /// If data is read from the queue and not fully used the remainder is stored back into the
    /// pending buffer.
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

impl<'a, T, A: Allocator> Read for Console<'a, T, A>
where
    T: VirtioTransport,
{
    fn read_exact(&mut self, data: &mut [u8]) -> anyhow::Result<()> {
        let len = data.len();
        let mut count = 0;
        while count < len {
            count += self.read_partial(&mut data[count..]).unwrap_or(0);
        }

        Ok(())
    }
}

impl<'a, T, A: Allocator> Write for Console<'a, T, A>
where
    T: VirtioTransport,
{
    fn write_all(&mut self, data: &[u8]) -> anyhow::Result<()> {
        let mut start = 0;
        let data_len = data.len();
        while start < data_len {
            let count = self.write_bytes(&data[start..]).unwrap_or(0);
            start += count;
        }
        Ok(())
    }

    fn flush(&mut self) -> anyhow::Result<()> {
        // We always flush on write, so do nothing.
        // TODO(#2876): We should use a buffered writer so that we don't always flush on write, and
        // provide an actual flush implementation here.
        Ok(())
    }
}

#[cfg(test)]
mod tests;
