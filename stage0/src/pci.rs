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

use core::{ffi::CStr, fmt::Display};

use oak_sev_guest::io::{IoPortFactory, PortReader, PortWriter};
use zerocopy::{FromBytes, FromZeros, IntoBytes};

use crate::{fw_cfg::Firmware, hal::Port, Platform};

#[repr(C)]
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, FromBytes, IntoBytes)]
pub struct PciCrsAllowlistEntry {
    pub address: u32,
    pub length: u32,
}
static_assertions::assert_eq_size!(PciCrsAllowlistEntry, [u8; 8]);

pub const PCI_CRS_ALLOWLIST_MAX_ENTRY_COUNT: usize = 11;

const PCI_CRS_ALLOWLIST_FILE_NAME: &CStr = c"etc/pci-crs-whitelist";

const PCI_PORT_CONFIGURATION_SPACE_ADDRESS: u16 = 0xCF8;
const PCI_PORT_CONFIGURATION_SPACE_DATA: u16 = 0xCFC;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct PciAddress {
    bus: u8,
    device: u8,   // 5 bits.
    function: u8, // 3 bits.
}

impl PciAddress {
    pub const fn new(bus: u8, device: u8, function: u8) -> Result<Self, &'static str> {
        if device > 0b11111 {
            return Err("invalid device number");
        }
        if function > 0b111 {
            return Err("invalid function number");
        }

        Ok(Self { bus, device, function })
    }
}

impl Display for PciAddress {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:02x}:{:02x}.{:x}", self.bus, self.device, self.function)
    }
}

/// Uses the legacy port-based IO method to read a u32 from the PCI
/// configuration space.
fn pci_read_cam<P: Platform>(address: PciAddress, offset: u8) -> Result<u32, &'static str> {
    let port_factory = P::port_factory();
    let mut address_port: Port<u32> = port_factory.new_writer(PCI_PORT_CONFIGURATION_SPACE_ADDRESS);
    let mut data_port: Port<u32> = port_factory.new_reader(PCI_PORT_CONFIGURATION_SPACE_DATA);

    let (bus, device, function) =
        (address.bus as u32, address.device as u32, address.function as u32);
    // Address register implemented per Section 3.2.2.3.2 of PCI spec, Rev 3.0.
    let value =
        (1u32 << 31) | (bus << 16) | (device << 11) | (function << 8) | ((offset as u32) << 2);
    // Safety: PCI_PORT_CONFIGURATION_SPACE_ADDRESS is a well-known port and should
    // be safe to write to even if we don't have a PCI bus.
    unsafe { address_port.try_write(value) }?;
    // Safety: PCI_PORT_CONFIGURATION_SPACE_DATA is a well-known port and should
    // be safe to read from even if we don't have a PCI bus (it'll return
    // 0xFFFFFFFF)
    unsafe { data_port.try_read() }
}

pub fn init<P: Platform>() -> Result<(), &'static str> {
    // At this point we know nothing about the platform we're on, so we have to
    // rely on the leagacy CAM to get the device ID of the first PCI root to
    // help us figure out on what kind of machine we are running.
    let root = PciAddress::new(0, 0, 0).unwrap();
    let (vendor_id, device_id) = {
        let value = pci_read_cam::<P>(root, 0x00)?;
        ((value & 0xFFFF) as u16, (value >> 16) as u16)
    };
    log::debug!("PCI root {}: {:04x}:{:04x}", root, vendor_id, device_id);

    Ok(())
}

pub fn read_pci_crs_allowlist(
    firmware: &mut dyn Firmware,
) -> Result<Option<[PciCrsAllowlistEntry; PCI_CRS_ALLOWLIST_MAX_ENTRY_COUNT]>, &'static str> {
    let file = match firmware.find(PCI_CRS_ALLOWLIST_FILE_NAME) {
        Some(file) => file,
        None => return Ok(None),
    };
    if file.size() % size_of::<PciCrsAllowlistEntry>() != 0 {
        return Err("invalid etc/pci-crs-whitelist file size");
    }
    if file.size() > PCI_CRS_ALLOWLIST_MAX_ENTRY_COUNT * size_of::<PciCrsAllowlistEntry>() {
        return Err("too many entries in etc/pci-crs-whitelist");
    }
    let mut entries = [PciCrsAllowlistEntry::new_zeroed(); PCI_CRS_ALLOWLIST_MAX_ENTRY_COUNT];
    firmware.read_file(&file, &mut entries.as_mut_bytes()[..file.size()])?;

    Ok(Some(entries))
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeMap, ffi::CString};

    use googletest::prelude::*;

    use super::*;

    #[derive(Default)]
    struct TestFirmware {
        pub files: BTreeMap<CString, Box<[u8]>>,
    }

    impl crate::fw_cfg::Firmware for TestFirmware {
        fn find(&mut self, name: &core::ffi::CStr) -> Option<crate::fw_cfg::DirEntry> {
            let file = self.files.get(name)?;
            Some(crate::fw_cfg::DirEntry::new(name, file.len() as u32, 0))
        }

        fn read_file(
            &mut self,
            file: &crate::fw_cfg::DirEntry,
            buf: &mut [u8],
        ) -> std::result::Result<usize, &'static str> {
            let file = self.files.get(file.name()).ok_or("file not found")?;
            buf.copy_from_slice(file);
            Ok(file.len())
        }
    }

    #[googletest::test]
    fn test_allowlist() {
        let mut firmware = TestFirmware::default();
        firmware
            .files
            .insert(PCI_CRS_ALLOWLIST_FILE_NAME.to_owned(), Box::new([1, 2, 3, 4, 5, 6, 7, 8]));

        let result = read_pci_crs_allowlist(&mut firmware);

        assert_that!(
            result,
            ok(some(all!(
                contains(eq(PciCrsAllowlistEntry { address: 0x04030201, length: 0x08070605 })),
                contains(eq(PciCrsAllowlistEntry::new_zeroed()))
            )))
        );
    }

    #[googletest::test]
    fn test_no_allowlist() {
        let mut firmware = TestFirmware::default();

        assert_that!(read_pci_crs_allowlist(&mut firmware), ok(none()));
    }

    #[googletest::test]
    fn test_allowlist_too_large() {
        let mut firmware = TestFirmware::default();
        firmware.files.insert(
            PCI_CRS_ALLOWLIST_FILE_NAME.to_owned(),
            Box::new([0; (PCI_CRS_ALLOWLIST_MAX_ENTRY_COUNT + 1) * 8]),
        );

        assert_that!(read_pci_crs_allowlist(&mut firmware), err(anything()));
    }

    #[googletest::test]
    fn test_allowlist_garbage() {
        let mut firmware = TestFirmware::default();
        firmware.files.insert(
            PCI_CRS_ALLOWLIST_FILE_NAME.to_owned(),
            Box::new([0; size_of::<PciCrsAllowlistEntry>() + 1]),
        );

        assert_that!(read_pci_crs_allowlist(&mut firmware), err(anything()));
    }
}
