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
    queue::{DeviceWriteOnlyQueue, DriverWriteOnlyQueue},
    vsock::packet::VSockOp,
};
use anyhow::Context;
use packet::Packet;
use rust_hypervisor_firmware_virtio::{
    device::VirtioBaseDevice,
    pci::{find_device, VirtioPciTransport},
};

pub mod packet;
pub mod socket;

/// The number of buffer descriptors in each of the queues.
const QUEUE_SIZE: usize = 16;

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

/// The vendor ID for virtio PCI devices.
const PCI_VENDOR_ID: u16 = 0x1AF4;

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
pub struct VSock {
    /// The base virtio-over-PCI device used for configuration and notification.
    device: VirtioBaseDevice<VirtioPciTransport>,
    /// The transmit queue.
    tx_queue: DriverWriteOnlyQueue<QUEUE_SIZE, DATA_BUFFER_SIZE>,
    /// The receive queue.
    rx_queue: DeviceWriteOnlyQueue<QUEUE_SIZE, DATA_BUFFER_SIZE>,
    /// The event queue used by the device to notify the driver that the guest CID has changed. We
    /// ignore it for now as we don't support live migration, but it still must exist and be
    /// configured.
    event_queue: DeviceWriteOnlyQueue<QUEUE_SIZE, EVENT_BUFFER_SIZE>,
    /// The the CID assigned to this VM.
    guest_cid: u64,
}

impl VSock {
    /// Finds the virtio vsock PCI device, initialises the device, and configures the queues.
    pub fn find_and_configure_device() -> anyhow::Result<Self> {
        // For now we just scan the first 32 devices on PCI bus 0 to find the first one that matches
        // the vendor ID and device ID.
        let pci_device = find_device(PCI_VENDOR_ID, PCI_DEVICE_ID)
            .ok_or_else(|| anyhow::anyhow!("Couldn't find a virtio vsock device."))?;
        let transport = VirtioPciTransport::new(pci_device);
        let device = VirtioBaseDevice::new(transport);
        let mut result = Self::new(device);
        result.init()?;
        Ok(result)
    }

    /// Reads the next valid packet from the receive queue, if one is available.
    pub fn read_packet(&mut self) -> Option<Packet> {
        loop {
            let buffer = self.rx_queue.read_next_used_buffer()?;
            if self.rx_queue.inner.must_notify_device() {
                // Notify the device that a packet has been read and the buffer is available again.
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

    /// Reads the next valid packet that matches the filter, if one is available.
    ///
    /// If invalid packets are found it will continue reading until a valid one is found, or no more
    /// packets are available to read.
    ///
    /// If `reset_unmatched` is true we send RST packets in response to unmatched packets to notify
    /// the host that the packets are not part of a valid connected socket (e.g. unexpected source
    /// or destintation ports) and any related connections on the host should be disconnected.
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
            // Notify the device that new packet has been written.
            self.device.notify_queue(TX_QUEUE_ID);
        }
    }

    fn new(device: VirtioBaseDevice<VirtioPciTransport>) -> Self {
        let tx_queue = DriverWriteOnlyQueue::new();
        let rx_queue = DeviceWriteOnlyQueue::new();
        let event_queue = DeviceWriteOnlyQueue::new();
        VSock {
            device,
            tx_queue,
            rx_queue,
            event_queue,
            guest_cid: Default::default(),
        }
    }

    /// Initializes the device and configures the queues.
    fn init(&mut self) -> anyhow::Result<()> {
        self.device
            .start_init(DEVICE_ID as u32)
            .map_err(|error| anyhow::anyhow!("Virtio error: {:?}", error))
            .context("Couldn't initialize the PCI device")?;
        self.device
            .configure_queue(
                RX_QUEUE_ID,
                QUEUE_SIZE as u16,
                self.rx_queue.inner.get_desc_addr(),
                self.rx_queue.inner.get_avail_addr(),
                self.rx_queue.inner.get_used_addr(),
            )
            .map_err(|error| anyhow::anyhow!("Queue configuration error: {:?}", error))
            .context("Couldn't configure the receive queue")?;
        self.device
            .configure_queue(
                TX_QUEUE_ID,
                QUEUE_SIZE as u16,
                self.tx_queue.inner.get_desc_addr(),
                self.tx_queue.inner.get_avail_addr(),
                self.tx_queue.inner.get_used_addr(),
            )
            .map_err(|error| anyhow::anyhow!("Queue configuration error: {:?}", error))
            .context("Couldn't configure the transmit queue")?;
        self.device
            .configure_queue(
                EVENT_QUEUE_ID,
                QUEUE_SIZE as u16,
                self.event_queue.inner.get_desc_addr(),
                self.event_queue.inner.get_avail_addr(),
                self.event_queue.inner.get_used_addr(),
            )
            .map_err(|error| anyhow::anyhow!("Queue configuration error: {:?}", error))
            .context("Couldn't configure the event queue")?;
        self.device
            .complete_init()
            .map_err(|error| anyhow::anyhow!("Device activation error: {:?}", error))
            .context("Couldn't activate the PCI device")?;

        // Read the guest CID from the PCI config. The upper 32 bits must be 0, so we only read the
        // lower 32 bits.
        self.guest_cid = self.device.get_config(CID_CONFIG_OFFSET) as u64;
        Ok(())
    }

    /// Sends a vsock RST packet indicating that a socket is disconnected, or must be forcibly
    /// disconnected.
    ///
    /// This is typically done in response to a packet with unexpected source or destination ports,
    /// an invalid op for the connection state, or to confirm that a socket has been diconnected.
    fn send_rst_packet(&mut self, host_port: u32, local_port: u32) {
        let mut packet = Packet::new_control(local_port, host_port, VSockOp::Rst).unwrap();
        self.write_packet(&mut packet);
    }
}
