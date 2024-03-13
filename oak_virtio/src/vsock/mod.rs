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

use anyhow::Context;
use packet::Packet;
use rust_hypervisor_firmware_virtio::{
    device::VirtioBaseDevice,
    pci::{find_device, VirtioPciTransport},
    virtio::VirtioTransport,
};

use crate::{
    queue::{DeviceWriteOnlyQueue, DriverWriteOnlyQueue},
    vsock::packet::VSockOp,
    InverseTranslator, Translator,
};

pub mod packet;
pub mod socket;

/// The number of buffer descriptors in each of the queues.
///
/// Note: We match the CrosVM max size for vhost vsock, as it seems CrosVM sets
/// the number of descriptors to the maximum queue size rather than the
/// negotiated size. See <https://chromium.googlesource.com/chromiumos/platform/crosvm/+/d4505a7f1c9e4aa502ff49367863aedeadbafb9d/devices/src/virtio/vhost/worker.rs#74>.
const QUEUE_SIZE: usize = 256;

/// The size of each of the buffers used by the transmit and receive queues.
const DATA_BUFFER_SIZE: usize = 4096;

/// The size of the buffers used by the event queue.
const EVENT_BUFFER_SIZE: usize = 8;

/// The id of the receive queue.
const RX_QUEUE_ID: u16 = 0;

/// The id of the transmit queue.
const TX_QUEUE_ID: u16 = 1;

/// The id of the event queue.
const EVENT_QUEUE_ID: u16 = 2;

/// The virtio device id for a socket device.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-1930005>.
const DEVICE_ID: u16 = 19;

/// The PCI device id for a virtio socket device.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-1020002>.
const PCI_DEVICE_ID: u16 = 0x1040 + DEVICE_ID;

/// The PCI config offset for reading the guest CID.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-3940004>.
const CID_CONFIG_OFFSET: u64 = 0;

/// The well-known host CID value.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-3940004>.
const HOST_CID: u64 = 2;

/// Low-level driver interface to interact with a virtio socket device.
///
/// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-39000010>.
pub struct VSock<'a, T: VirtioTransport, A: Allocator> {
    /// The base virtio-over-PCI device used for configuration and notification.
    device: VirtioBaseDevice<T>,
    /// The receive queue.
    rx_queue: DeviceWriteOnlyQueue<'a, QUEUE_SIZE, DATA_BUFFER_SIZE, A>,
    /// The transmit queue.
    tx_queue: DriverWriteOnlyQueue<'a, QUEUE_SIZE, DATA_BUFFER_SIZE, A>,
    /// The event queue used by the device to notify the driver that the guest
    /// CID has changed. We ignore it for now as we don't support live
    /// migration, but it still must exist and be configured.
    event_queue: DeviceWriteOnlyQueue<'a, QUEUE_SIZE, EVENT_BUFFER_SIZE, A>,
    /// The the CID assigned to this VM.
    guest_cid: u64,
}

impl<'a, A: Allocator> VSock<'a, VirtioPciTransport, A> {
    /// Finds the virtio vsock PCI device, initialises the device, and
    /// configures the queues.
    pub fn find_and_configure_device<VP: Translator, PV: InverseTranslator>(
        translate: VP,
        inverse: PV,
        alloc: &'a A,
    ) -> anyhow::Result<Self> {
        // For now we just scan the first 32 devices on PCI bus 0 to find the first one
        // that matches the vendor ID and device ID.
        let pci_device = find_device(super::PCI_VENDOR_ID, PCI_DEVICE_ID)
            .ok_or_else(|| anyhow::anyhow!("couldn't find a virtio vsock device"))?;
        let transport = VirtioPciTransport::new(pci_device);
        let device = VirtioBaseDevice::new(transport);
        let mut result = Self::new(device, &translate, alloc);
        result.init(translate, inverse)?;
        // Let the device know there are available buffers in the receiver and event
        // queues.
        result.device.notify_queue(RX_QUEUE_ID);
        result.device.notify_queue(EVENT_QUEUE_ID);
        Ok(result)
    }
}

impl<'a, T, A: Allocator> VSock<'a, T, A>
where
    T: VirtioTransport,
{
    /// Reads the next valid packet from the receive queue, if one is available.
    pub fn read_packet(&mut self) -> Option<Packet> {
        loop {
            let buffer = self.rx_queue.read_next_used_buffer()?;
            if self.rx_queue.inner.must_notify_device() {
                // Notify the device that a packet has been read and the buffer is available
                // again.
                self.device.notify_queue(RX_QUEUE_ID);
            }
            // Silently drop packets where the CIDs don't match.
            if let Ok(packet) = Packet::new(buffer) {
                if packet.get_src_cid() == HOST_CID && packet.get_dst_cid() == self.guest_cid {
                    return Some(packet);
                }
            }
        }
    }

    /// Reads the next valid packet that matches the filter, if one is
    /// available.
    ///
    /// If invalid packets are found it will continue reading until a valid one
    /// is found, or no more packets are available to read.
    ///
    /// If `reset_unmatched` is true we send RST packets in response to
    /// unmatched packets to notify the host that the packets are not part
    /// of a valid connected socket (e.g. unexpected source or destintation
    /// ports) and any related connections on the host should be disconnected.
    pub fn read_filtered_packet<F: Fn(&Packet) -> bool>(
        &mut self,
        filter: F,
        reset_unmatched: bool,
    ) -> Option<Packet> {
        loop {
            let packet = self.read_packet()?;
            if filter(&packet) {
                return Some(packet);
            }
            if reset_unmatched {
                self.send_rst_packet(packet.get_src_port(), packet.get_dst_port())
            }
        }
    }

    /// Writes the packet to the transmit queue.
    pub fn write_packet(&mut self, packet: &mut Packet) {
        // Ensure that the CIDs are set correctly.
        packet.set_dst_cid(HOST_CID);
        packet.set_src_cid(self.guest_cid);

        self.tx_queue.write_buffer(packet.as_slice());

        if self.tx_queue.inner.must_notify_device() {
            // Notify the device that a new packet has been written.
            self.device.notify_queue(TX_QUEUE_ID);
        }
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
        let event_queue = DeviceWriteOnlyQueue::new(&translate, alloc);
        VSock { device, tx_queue, rx_queue, event_queue, guest_cid: Default::default() }
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
        // We have to configure the event queue before the receive queue, otherwise the
        // event queue's configuration interferes with the receiver queue. This
        // seems to be related to something specific in the Linux kernel vhost
        // vsock implementation.
        self.device
            .configure_queue(
                EVENT_QUEUE_ID,
                QUEUE_SIZE as u16,
                translate(self.event_queue.inner.get_desc_addr())
                    .context("couldn't translate VirtAddr to PhysAddr")?,
                translate(self.event_queue.inner.get_avail_addr())
                    .context("couldn't translate VirtAddr to PhysAddr")?,
                translate(self.event_queue.inner.get_used_addr())
                    .context("couldn't translate VirtAddr to PhysAddr")?,
            )
            .map_err(|error| anyhow::anyhow!("queue configuration error: {:?}", error))
            .context("couldn't configure the event queue")?;
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

        // Read the guest CID from the PCI config. The upper 32 bits must be 0, so we
        // only read the lower 32 bits.
        self.guest_cid = self.device.get_config(CID_CONFIG_OFFSET) as u64;
        Ok(())
    }

    /// Sends a vsock RST packet indicating that a socket is disconnected, or
    /// must be forcibly disconnected.
    ///
    /// This is typically done in response to a packet with unexpected source or
    /// destination ports, an invalid op for the connection state, or to
    /// confirm that a socket has been diconnected.
    fn send_rst_packet(&mut self, host_port: u32, local_port: u32) {
        let mut packet = Packet::new_control(local_port, host_port, VSockOp::Rst).unwrap();
        self.write_packet(&mut packet);
    }
}

#[cfg(test)]
mod tests;
