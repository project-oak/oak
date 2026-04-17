//
// Copyright 2025 The Project Oak Authors
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

use oak_sev_guest::io::{IoPortFactory, PortReader, PortWriter};

use crate::{Platform, hal::Port, pci::device::Bdf};

#[cfg_attr(test, mockall::automock)]
pub trait ConfigAccess {
    fn read(&mut self, address: Bdf, offset: u8) -> Result<u32, &'static str>;
    fn write(&mut self, address: Bdf, offset: u8, value: u32) -> Result<(), &'static str>;
}

#[allow(clippy::upper_case_acronyms)]
/// Uses the legacy port-based IO method to read a u32 from the PCI
/// configuration space.
pub struct CAM {
    address_port: Port<u32>,
    data_port: Port<u32>,
}

impl CAM {
    const PCI_PORT_CONFIGURATION_SPACE_ADDRESS: u16 = 0xCF8;
    const PCI_PORT_CONFIGURATION_SPACE_DATA: u16 = 0xCFC;

    pub fn new<P: Platform>() -> Self {
        let port_factory = P::port_factory();
        Self {
            address_port: port_factory.new_writer(Self::PCI_PORT_CONFIGURATION_SPACE_ADDRESS),
            data_port: port_factory.new_reader(Self::PCI_PORT_CONFIGURATION_SPACE_DATA),
        }
    }
}

impl ConfigAccess for CAM {
    fn read(&mut self, address: Bdf, offset: u8) -> Result<u32, &'static str> {
        // Address register implemented per Section 3.2.2.3.2 of PCI spec, Rev 3.0.
        let value =
            (1u32 << 31) | ((Into::<u16>::into(address) as u32) << 8) | ((offset as u32) << 2);
        // Safety: PCI_PORT_CONFIGURATION_SPACE_ADDRESS is a well-known port and should
        // be safe to write to even if we don't have a PCI bus.
        unsafe { self.address_port.try_write(value) }?;
        // Safety: PCI_PORT_CONFIGURATION_SPACE_DATA is a well-known port and should
        // be safe to read from even if we don't have a PCI bus (it'll return
        // 0xFFFFFFFF)
        unsafe { self.data_port.try_read() }
    }

    fn write(&mut self, address: Bdf, offset: u8, value: u32) -> Result<(), &'static str> {
        // Address register implemented per Section 3.2.2.3.2 of PCI spec, Rev 3.0.
        let address =
            (1u32 << 31) | ((Into::<u16>::into(address) as u32) << 8) | ((offset as u32) << 2);
        // Safety: PCI_PORT_CONFIGURATION_SPACE_ADDRESS is a well-known port and should
        // be safe to write to even if we don't have a PCI bus.
        unsafe { self.address_port.try_write(address) }?;
        // Safety: PCI_PORT_CONFIGURATION_SPACE_DATA is a well-known port and should
        // be safe to write to even if we don't have a PCI bus.
        unsafe { self.data_port.try_write(value) }
    }
}
