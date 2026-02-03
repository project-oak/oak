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

use alloc::{boxed::Box, string::String, vec::Vec};
use core::ptr::NonNull;

use acpi::{AcpiHandler, AcpiTables, AmlTable, PhysicalMapping};
use aml::{
    AmlContext, AmlError, AmlName, AmlValue, LevelType, NamespaceLevel,
    resource::{MemoryRangeDescriptor, Resource, resource_descriptor_list},
    value::Args,
};
use anyhow::{Result, anyhow, bail};
use oak_linux_boot_params::BootParams;
use x86_64::PhysAddr;

use crate::{PAGE_TABLES, mm::Translator};

/// Table of well-known ACPI devices (or, rather, well-known to us)
const ACPI_GED: &str = "ACPI0013";
pub const VIRTIO_MMIO: &str = "LNRO0005";
const SERIAL_PORT: &str = "PNP0501";
const PCI_BUS: &str = "PNP0A03";
const PCIE_BUS: &str = "PNP0A08";
const POWER_BUTTON: &str = "PNP0C0C";
const QEMU_FW_CFG_DEVICE_ID: &str = "QEMU0002";

fn description(hid: &str) -> &str {
    match hid {
        ACPI_GED => "ACPI Generic Event Device",
        VIRTIO_MMIO => "Memory-mapped virtio device bus",
        SERIAL_PORT => "16550A-compatible COM Serial Port",
        PCI_BUS => "PCI bus",
        PCIE_BUS => "PCI Express bus",
        POWER_BUTTON => "Power Button Device",
        QEMU_FW_CFG_DEVICE_ID => "QEMU fw_cfg Device",
        _ => "(unknown device)",
    }
}

#[derive(Copy, Clone)]
struct Handler {}
impl AcpiHandler for Handler {
    unsafe fn map_physical_region<T>(
        &self,
        physical_address: usize,
        size: usize,
    ) -> PhysicalMapping<Self, T> {
        unsafe {
            PhysicalMapping::new(
                physical_address,
                NonNull::new(
                    PAGE_TABLES
                        .lock()
                        .get()
                        .unwrap()
                        .translate_physical(PhysAddr::new(physical_address as u64))
                        .unwrap()
                        .as_mut_ptr(),
                )
                .unwrap(),
                size,
                size,
                *self,
            )
        }
    }

    fn unmap_physical_region<T>(_region: &acpi::PhysicalMapping<Self, T>) {
        // Nothing to do here.
    }
}

impl aml::Handler for Handler {
    fn read_u8(&self, _address: usize) -> u8 {
        unimplemented!()
    }

    fn read_u16(&self, _address: usize) -> u16 {
        unimplemented!()
    }

    fn read_u32(&self, _address: usize) -> u32 {
        unimplemented!()
    }

    fn read_u64(&self, _address: usize) -> u64 {
        unimplemented!()
    }

    fn write_u8(&mut self, _address: usize, _value: u8) {
        unimplemented!()
    }

    fn write_u16(&mut self, _address: usize, _value: u16) {
        unimplemented!()
    }

    fn write_u32(&mut self, _address: usize, _value: u32) {
        unimplemented!()
    }

    fn write_u64(&mut self, _address: usize, _value: u64) {
        unimplemented!()
    }

    fn read_io_u8(&self, port: u16) -> u8 {
        log::error!("unexpected call to `read_io_u8`: port {:#x}", port);
        0
    }

    fn read_io_u16(&self, _port: u16) -> u16 {
        unimplemented!()
    }

    fn read_io_u32(&self, _port: u16) -> u32 {
        unimplemented!()
    }

    fn write_io_u8(&self, _port: u16, _value: u8) {
        unimplemented!()
    }

    fn write_io_u16(&self, _port: u16, _value: u16) {
        unimplemented!()
    }

    fn write_io_u32(&self, _port: u16, _value: u32) {
        unimplemented!()
    }

    fn read_pci_u8(&self, segment: u16, bus: u8, device: u8, function: u8, offset: u16) -> u8 {
        log::error!(
            "unexpected call to `read_pci_u8`: segment {}, bus {}, device {}, function {}, offset {}",
            segment,
            bus,
            device,
            function,
            offset
        );
        0
    }

    fn read_pci_u16(
        &self,
        _segment: u16,
        _bus: u8,
        _device: u8,
        _function: u8,
        _offset: u16,
    ) -> u16 {
        unimplemented!()
    }

    fn read_pci_u32(
        &self,
        _segment: u16,
        _bus: u8,
        _device: u8,
        _function: u8,
        _offset: u16,
    ) -> u32 {
        unimplemented!()
    }

    fn write_pci_u8(
        &self,
        _segment: u16,
        _bus: u8,
        _device: u8,
        _function: u8,
        _offset: u16,
        _value: u8,
    ) {
        unimplemented!()
    }

    fn write_pci_u16(
        &self,
        _segment: u16,
        _bus: u8,
        _device: u8,
        _function: u8,
        _offset: u16,
        _value: u16,
    ) {
        unimplemented!()
    }

    fn write_pci_u32(
        &self,
        _segment: u16,
        _bus: u8,
        _device: u8,
        _function: u8,
        _offset: u16,
        _value: u32,
    ) {
        unimplemented!()
    }
}

trait TableContents<'a> {
    fn contents(&self) -> &'a [u8];
}
impl<'a> TableContents<'a> for AmlTable {
    fn contents(&self) -> &'a [u8] {
        let virt_addr = PAGE_TABLES
            .lock()
            .get()
            .unwrap()
            .translate_physical(PhysAddr::new(self.address as u64))
            .unwrap();
        // Safety: this address was specified in the ACPI tables by the firmware, so if
        // the tables are correct, this is safe.
        unsafe { core::slice::from_raw_parts(virt_addr.as_ptr(), self.length as usize) }
    }
}

/// Translates an EISA ID (a compressed 32-bit identifier) to its string
/// representation.
///
/// For the full specification, see the Plug and Play BIOS Specification (the
/// latest of which seems to be v1.0a from 1994), but in short:
/// The EISA ID is a 32-bit identifier that encodes a 8-character ASCII string
/// as follows: 0b0_AAAAA_BBBBB_CCCCC_1111_2222_3333_4444
///   - The 31th bit is always 0.
///   - Bits 30..26, 25..21, 20..16 (five bits each) encode the compressed
///     three-letter manufacturer ID; the compression algorithm is the lowest 5
///     bits of (character - 0x40).
///   - Bits 15..12, 11..8, 7..4, 3..0 (four bits each) encode a hexadecimal
///     digit.
///
/// As to what the IDs map to, as the specfication says, look for "Device
/// Identifier Reference Table & Device Type Code Table" on the PlugPlay forum
/// on CompuServe.
fn name_from_eisa_id(eisa_id: u64) -> Result<String, AmlError> {
    let eisa_id: u32 = u32::from_be(eisa_id.try_into().map_err(|_| AmlError::InvalidNameSeg)?);
    let mut str = String::with_capacity(7);

    for x in [26, 21, 16].iter() {
        str.push(
            char::from_u32(0x40 + ((eisa_id & (0b11111u32 << x)) >> x))
                .ok_or(AmlError::InvalidNameSeg)?,
        );
    }
    for x in [12, 8, 4, 0].iter() {
        str.push(
            char::from_digit((eisa_id & (0b1111u32 << x)) >> x, 0xF)
                .ok_or(AmlError::InvalidNameSeg)?
                .to_ascii_uppercase(),
        );
    }

    Ok(str)
}

pub struct AcpiDevice {
    pub name: AmlName,
}

impl AcpiDevice {
    /// Return the value of the `_HID` object, if present.
    ///
    /// ACPI specifications require one of `_HID` or `_ADR` to be present.
    /// See Section 6.1 of the ACPI spec for more details.
    pub fn hid(&self, ctx: &mut AmlContext) -> Result<Option<String>> {
        let hid = self.invoke("_HID", ctx);

        if let Ok(hid) = hid {
            // If the name is an integer, it's a compressed EISA identifier (yes, really).
            let hid = match hid {
                AmlValue::String(s) => Ok(s),
                AmlValue::Integer(i) => name_from_eisa_id(i),
                _ => Err(AmlError::InvalidNameSeg),
            }
            .map_err(|err| anyhow!("error parsing HID value: {:?}", err))?;
            Ok(Some(hid))
        } else {
            Ok(None)
        }
    }

    /// Return the valuie of the `_CRS` object, if present.
    ///
    /// CRS stands for Current Resource Settings; see Section 6.2 of the ACPI
    /// spec for more details.
    pub fn crs(&self, ctx: &mut AmlContext) -> Result<Option<Vec<Resource>>> {
        let crs = self.invoke("_CRS", ctx).map_err(|err| anyhow!("error resolving CRS: {:?}", err));

        if let Ok(crs) = crs {
            let resources = resource_descriptor_list(&crs)
                .map_err(|err| anyhow!("error building resource descriptor list: {:?}", err))?;
            Ok(Some(resources))
        } else {
            Ok(None)
        }
    }

    fn invoke(&self, object: &str, ctx: &mut AmlContext) -> Result<AmlValue, AmlError> {
        let object_name = AmlName::from_str(object)?;
        ctx.invoke_method(&object_name.resolve(&self.name)?, Args::default())
    }
}

pub struct Acpi {
    tables: AcpiTables<Handler>,
    pub aml: AmlContext,
}

impl Acpi {
    pub fn new(params: &BootParams) -> Result<Self> {
        let mut acpi = Self {
            tables: find_acpi_tables(params)?,
            aml: AmlContext::new(Box::new(Handler {}), aml::DebugVerbosity::None),
        };

        // Parse the DSDT and all SSDTs.
        if let Ok(ref dsdt) = acpi.tables.dsdt() {
            acpi.aml
                .parse_table(dsdt.contents())
                .map_err(|err| anyhow!("failed to parse ACPI DSDT: {:?}", err))?;
        } else {
            bail!("no DSDT found in ACPI tables");
        }

        for ssdt in acpi.tables.ssdts() {
            acpi.aml.parse_table(ssdt.contents()).map_err(|err| {
                anyhow!("failed to parse ACPI SSDT at address {}: {:?}", ssdt.address, err)
            })?;
        }

        acpi.aml
            .initialize_objects()
            .map_err(|err| anyhow!("failed to initialize ACPI AML objects: {:?}", err))?;

        Ok(acpi)
    }

    pub fn devices(&mut self) -> Result<Vec<AcpiDevice>> {
        self.walk(|_aml, name, _level| Ok(Some(AcpiDevice { name: name.clone() })))
    }

    fn walk<F, T>(&mut self, f: F) -> Result<Vec<T>>
    where
        F: Fn(&mut AmlContext, &AmlName, &NamespaceLevel) -> Result<Option<T>, AmlError>,
    {
        let mut results = Vec::new();
        self.aml
            .namespace
            .clone()
            .traverse(|name, level| match level.typ {
                LevelType::Device => {
                    if let Some(result) = f(&mut self.aml, name, level)? {
                        results.push(result);
                    }
                    Ok(true)
                }
                LevelType::Scope => Ok(true),
                _ => Ok(false),
            })
            .map_err(|err| anyhow!("failed to walk ACPI tables: {:?}", err))?;
        Ok(results)
    }

    pub fn print_devices(&mut self) -> Result<()> {
        for device in self.devices()? {
            if let Some(hid) = device.hid(&mut self.aml)? {
                log::info!("ACPI device: {} {:7} {}", device.name, hid, description(hid.as_str()));
            } else {
                log::info!("ACPI device: {} (no HID)", device.name);
            }

            if let Some(ref resources) = device.crs(&mut self.aml)? {
                for resource in resources {
                    match resource {
                        Resource::Irq(irq) => log::info!("  IRQ: {}", irq.irq),
                        Resource::AddressSpace(address) => {
                            log::info!("  Address space: {:?}", address)
                        }
                        Resource::MemoryRange(MemoryRangeDescriptor::FixedLocation {
                            is_writable: _,
                            base_address,
                            range_length,
                        }) => log::info!(
                            "  Memory range: [{:#018x}..{:#018x})",
                            base_address,
                            base_address + range_length
                        ),
                        Resource::IOPort(port) => log::info!("  IO port: {:?}", port),
                        Resource::Dma(dma) => log::info!("  DMA: {:?}", dma),
                    }
                }
            }
        }
        Ok(())
    }
}

fn find_acpi_tables(params: &BootParams) -> Result<AcpiTables<Handler>> {
    let acpi_rsdp_addr = params.acpi_rsdp_addr;
    if acpi_rsdp_addr > 0 {
        // Safety: we trust the boot params to be correct.
        return unsafe { AcpiTables::from_rsdp(Handler {}, params.acpi_rsdp_addr as usize) }
            .map_err(|err| {
                anyhow!(
                    "failed to load ACPI tables from address {:#x} specified in boot params: {:?}",
                    acpi_rsdp_addr,
                    err
                )
            });
    }

    // Safety: the EBDA area will be mapped and valid, so this is memory-safe, but
    // we're still searching 1 KiB of memory for the signature that may not be
    // there or match some random garbage.
    unsafe { AcpiTables::search_for_rsdp_bios(Handler {}) }
        .map_err(|err| anyhow!("failed to load ACPI tables from EBDA: {:?}", err))
}
