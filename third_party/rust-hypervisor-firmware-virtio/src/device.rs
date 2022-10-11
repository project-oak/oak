// Copyright © 2019 Intel Corporation
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
// Copyright 2022 The Project Oak Authors
// SPDX-License-Identifier: Apache-2.0
//

use x86_64::PhysAddr;

use crate::{
    virtio::{Error as VirtioError, VirtioTransport},
    InverseTranslator,
};

// Virtio Version 1 feature bit.
// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-4100006>.
const VIRTIO_F_VERSION_1: u64 = 1 << 32;

// Status fields.
// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-100001>.
const VIRTIO_STATUS_RESET: u32 = 0;
const VIRTIO_STATUS_ACKNOWLEDGE: u32 = 1;
const VIRTIO_STATUS_DRIVER: u32 = 2;
const VIRTIO_STATUS_FEATURES_OK: u32 = 8;
const VIRTIO_STATUS_DRIVER_OK: u32 = 4;
const VIRTIO_STATUS_FAILED: u32 = 128;

#[repr(C)]
#[repr(align(64))]
/// Device driver for virtio block over any transport
pub struct VirtioBaseDevice<T: VirtioTransport> {
    transport: T,
}

impl<T> VirtioBaseDevice<T>
where
    T: VirtioTransport,
{
    pub fn new(transport: T) -> Self {
        Self { transport }
    }

    /// Start Initialising the device.
    ///
    /// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-920001>.
    pub fn start_init<X: InverseTranslator>(
        &mut self,
        device_type: u32,
        translate: X,
    ) -> Result<(), VirtioError> {
        // Initialise the transport.
        self.transport.init(device_type, translate)?;

        // Reset device.
        self.transport.set_status(VIRTIO_STATUS_RESET);

        // Acknowledge.
        self.transport.add_status(VIRTIO_STATUS_ACKNOWLEDGE);

        // And advertise driver.
        self.transport.add_status(VIRTIO_STATUS_DRIVER);

        // Request device features.
        let device_features = self.transport.get_features();

        if device_features & VIRTIO_F_VERSION_1 != VIRTIO_F_VERSION_1 {
            self.transport.add_status(VIRTIO_STATUS_FAILED);
            return Err(VirtioError::LegacyOnly);
        }

        // Don't support any advanced features for now.
        let supported_features = VIRTIO_F_VERSION_1;

        // Report driver features.
        self.transport
            .set_features(device_features & supported_features);

        self.transport.add_status(VIRTIO_STATUS_FEATURES_OK);
        if self.transport.get_status() & VIRTIO_STATUS_FEATURES_OK != VIRTIO_STATUS_FEATURES_OK {
            self.transport.add_status(VIRTIO_STATUS_FAILED);
            return Err(VirtioError::FeatureNegotiationFailed);
        }
        Ok(())
    }

    /// Sets the configuration for a queue and enables it.
    ///
    /// Must be called for each queue after `start_init` was called.
    pub fn configure_queue(
        &mut self,
        queue_id: u16,
        queue_size: u16,
        desc_addr: PhysAddr,
        avail_addr: PhysAddr,
        used_addr: PhysAddr,
    ) -> Result<(), VirtioError> {
        self.transport.set_queue(queue_id);

        // Ensure driver queue is not too large for the device.
        let max_queue = self.transport.get_queue_max_size();
        if max_queue < queue_size {
            self.transport.add_status(VIRTIO_STATUS_FAILED);
            return Err(VirtioError::QueueTooSmall);
        }
        self.transport.set_queue_size(queue_size);

        // Set the address of the descriptor table.
        self.transport.set_descriptors_address(desc_addr);

        // Set the address of the available ring.
        self.transport.set_avail_ring(avail_addr);

        // Set the address of the used ring.
        self.transport.set_used_ring(used_addr);

        // Confirm queue is configured.
        self.transport.set_queue_enable();

        Ok(())
    }

    /// Completes the configuration of the device.
    ///
    /// Must be called once all the queues are initialised, before starting to use the device.
    pub fn complete_init(&mut self) -> Result<(), VirtioError> {
        // Report driver ready.
        self.transport.add_status(VIRTIO_STATUS_DRIVER_OK);

        Ok(())
    }

    /// Reads 32 bits of a config value from the transport.
    pub fn get_config(&self, offset: u64) -> u32 {
        self.transport.read_device_config(offset)
    }

    /// Gets the device status.
    ///
    /// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-100001>.
    pub fn get_status(&self) -> u32 {
        self.transport.get_status()
    }

    /// Notifies the device that a queue has been updated.
    pub fn notify_queue(&mut self, queue_id: u16) {
        self.transport.notify_queue(queue_id)
    }
}
