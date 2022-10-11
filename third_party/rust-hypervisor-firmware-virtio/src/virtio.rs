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

use x86_64::PhysAddr;

use crate::InverseTranslator;

/// Virtio related errors
#[derive(Debug)]
pub enum Error {
    UnsupportedDevice,
    LegacyOnly,
    FeatureNegotiationFailed,
    QueueTooSmall,
    AddressTranslationFailure(PhysAddr),
}

/// Trait to allow separation of transport from block driver
pub trait VirtioTransport {
    fn init<X: InverseTranslator>(&mut self, device_type: u32, translate: X) -> Result<(), Error>;
    fn get_status(&self) -> u32;
    fn set_status(&self, status: u32);
    fn add_status(&self, status: u32);
    fn reset(&self);
    fn get_features(&self) -> u64;
    fn set_features(&self, features: u64);
    fn set_queue(&self, queue: u16);
    fn get_queue_max_size(&self) -> u16;
    fn set_queue_size(&self, queue_size: u16);
    fn set_descriptors_address(&self, address: PhysAddr);
    fn set_avail_ring(&self, address: PhysAddr);
    fn set_used_ring(&self, address: PhysAddr);
    fn set_queue_enable(&self);
    fn notify_queue(&self, queue: u16);
    fn read_device_config(&self, offset: u64) -> u32;
}
