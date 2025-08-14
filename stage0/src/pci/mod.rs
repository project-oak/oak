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

use core::{
    ffi::CStr,
    fmt::Display,
    marker::PhantomData,
    ops::{Add, Range},
};

use oak_sev_guest::io::{IoPortFactory, PortReader, PortWriter};
use strum::FromRepr;
use x86_64::align_down;
use zerocopy::{FromBytes, FromZeros, IntoBytes};

use crate::{fw_cfg::Firmware, hal::Port, Platform, ZeroPage};

#[repr(C)]
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, FromBytes, IntoBytes)]
pub struct PciCrsAllowlistEntry {
    pub address: u32,
    pub length: u32,
}
static_assertions::assert_eq_size!(PciCrsAllowlistEntry, [u8; 8]);

pub const PCI_CRS_ALLOWLIST_MAX_ENTRY_COUNT: usize = 11;

const PCI_CRS_ALLOWLIST_FILE_NAME: &CStr = c"etc/pci-crs-whitelist";
const EXTRA_ROOTS_FILE_NAME: &CStr = c"etc/extra-pci-roots";
const PCI_MMIO32_HOLE_BASE_FILE_NAME: &CStr = c"etc/pci-mmio32-hole-base";
const MMCFG_MEM_RESERVATION_FILE: &CStr = c"etc/mmcfg_mem_reservation";

const PCI_PORT_CONFIGURATION_SPACE_ADDRESS: u16 = 0xCF8;
const PCI_PORT_CONFIGURATION_SPACE_DATA: u16 = 0xCFC;

/// PCI class codes.
///
/// We use a struct instead of enum because Rust enums are closed, but we will
/// not give an exhaustive list of class codes.
///
/// See the PCI Code and ID Assignment Specification on pcisig.com for the
/// authoritative source.
#[derive(PartialEq, Eq)]
#[repr(transparent)]
struct PciClass(pub u8);

impl PciClass {
    pub const BRIDGE: PciClass = PciClass(0x06);
}

impl Display for PciClass {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:02x}", self.0)
    }
}
/// Subclass types for PCI devices
///
/// Again, we only list a subset, so we use a struct instead of an enum.
///
/// See the PCI Code and ID Assignment Specification on pcisig.com for the
/// authoritative source.
#[derive(PartialEq, Eq)]
#[repr(transparent)]
struct PciSubclass(pub u8);
impl PciSubclass {
    #[allow(dead_code)]
    pub const HOST_BRIDGE: PciSubclass = PciSubclass(0x00);
    pub const PCI_TO_PCI_BRIDGE: PciSubclass = PciSubclass(0x04);
}

impl Display for PciSubclass {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:02x}", self.0)
    }
}

#[derive(Debug, FromBytes, IntoBytes)]
#[repr(C, packed)]
#[allow(dead_code)]
struct PciBridgeBusRegister {
    pub secondary_latency_timer: u8,
    pub subordinate_bus_number: u8,
    pub secondary_bus_number: u8,
    pub primary_bus_number: u8,
}

struct MemoryBar<T> {
    offset: u8,
    bar_size: T,
}

struct IoBar {
    offset: u8,
    bar_size: u32,
}

enum PciBar<'a> {
    Memory32(&'a PciAddress, MemoryBar<u32>),
    Memory64(&'a PciAddress, MemoryBar<u64>),
    Io(&'a PciAddress, IoBar),
}

#[derive(FromRepr, PartialEq)]
#[repr(u32)]
/// Values representing the two kinds of PCI BARs.
enum PciBarKind {
    Memory = 0b0,
    Io = 0b1,
}

impl PciBarKind {
    const MASK: u32 = 0b1;
}

#[derive(FromRepr, Debug, PartialEq)]
#[repr(u32)]
enum PciMemoryBarSize {
    Size32 = 0b000,
    // 0b010 -- reserved
    Size64 = 0b100,
    // 0b110 -- unused
}
impl PciMemoryBarSize {
    const MASK: u32 = 0b110;
}

struct BarIter<'a, P: Platform> {
    device: &'a PciAddress,
    // Bridges have up to 2 BARs, normal devices 6.
    max_bars: u8,
    index: Option<u8>,
    _phantom: PhantomData<P>,
}

impl<'a, P: Platform> Iterator for BarIter<'a, P> {
    type Item = PciBar<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        // Try to find a next BAR.
        loop {
            self.index = self.index.filter(|&index| index < self.max_bars);
            let index = self.index?;
            let offset = 0x4 + index;

            // Proble the BAR by writing all-ones.
            pci_write_cam::<P>(self.device, offset, 0xFFFF_FFFF).ok()?;
            let value = pci_read_cam::<P>(self.device, offset).ok()?;

            if value == 0 {
                // Unimplemented BAR.
                let _ = self.index.insert(index + 1);
                continue;
            }

            // We have a valid BAR. I/O and 32-bit memory BARs take one slot,
            // 64-bit memory BARs two slots.
            let bar_type = PciBarKind::from_repr(value & PciBarKind::MASK)?;

            match bar_type {
                PciBarKind::Memory => {
                    let size = PciMemoryBarSize::from_repr(value & PciMemoryBarSize::MASK)?;
                    // Mask away all but the BAR size field.
                    let value = value & !0b1111;

                    if size == PciMemoryBarSize::Size64 {
                        // For 64-bit BARs, we need to read the next register as well.
                        pci_write_cam::<P>(self.device, offset + 1, 0xFFFF_FFFF).ok()?;
                        let upper_half = pci_read_cam::<P>(self.device, offset + 1).ok()? as u64;
                        let _ = self.index.insert(index + 2);

                        return Some(PciBar::Memory64(
                            self.device,
                            MemoryBar {
                                offset: index,
                                bar_size: !((upper_half << 32) + (value as u64)) + 1,
                            },
                        ));
                    } else {
                        let _ = self.index.insert(index + 1);
                        return Some(PciBar::Memory32(
                            self.device,
                            MemoryBar { offset: index, bar_size: !value + 1 },
                        ));
                    }
                }
                PciBarKind::Io => {
                    let value = value & !0b1;
                    let _ = self.index.insert(index + 1);
                    return Some(PciBar::Io(
                        self.device,
                        IoBar { offset: index, bar_size: !value + 1 },
                    ));
                }
            }
        }
    }
}

/// PCI address.
///
/// Basic structure: BBBBBBBBDDDDDFFF
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(transparent)]
struct PciAddress(u16);

impl PciAddress {
    pub const fn new(bus: u8, device: u8, function: u8) -> Result<Self, &'static str> {
        if device > 0b11111 {
            return Err("invalid device number");
        }
        if function > 0b111 {
            return Err("invalid function number");
        }

        Ok(Self((bus as u16) << 8 | (device as u16) << 3 | (function as u16)))
    }

    /// Returns the Vendor ID and Device ID for the address.
    fn vendor_device_id<P: Platform>(&self) -> Result<(u16, u16), &'static str> {
        // Register 0x00: Device ID, Vendor ID (16b each)
        let value = pci_read_cam::<P>(self, 0x00)?;
        Ok(((value & 0xFFFF) as u16, (value >> 16) as u16))
    }

    fn class_code<P: Platform>(&self) -> Result<(PciClass, PciSubclass), &'static str> {
        // Register 0x02: Class Code, Subclass, Prog IF, Revision ID (8b each)
        let value = pci_read_cam::<P>(self, 0x02)?;
        Ok((PciClass((value >> 24) as u8), PciSubclass((value >> 16) as u8)))
    }

    // Returns the header type for the address.
    fn header_type<P: Platform>(&self) -> Result<u8, &'static str> {
        // Register 0x03: BIST, header type, latency timer, cache line size (8b each)
        let value = pci_read_cam::<P>(self, 0x03)?;
        Ok((value >> 16) as u8)
    }

    fn bridge_bus_numbers<P: Platform>(&self) -> Result<PciBridgeBusRegister, &'static str> {
        let value = pci_read_cam::<P>(self, 0x06)?;
        Ok(PciBridgeBusRegister::read_from_bytes(value.as_bytes()).unwrap())
    }

    fn is_multi_function_device<P: Platform>(&self) -> Result<bool, &'static str> {
        self.header_type::<P>().map(|value| value & 0x80 != 0)
    }

    fn iter_bars<P: Platform>(&self) -> Result<BarIter<'_, P>, &'static str> {
        let (class, subclass) = self.class_code::<P>()?;
        let max_bars = if class == PciClass::BRIDGE && subclass == PciSubclass::PCI_TO_PCI_BRIDGE {
            2
        } else {
            6
        };
        Ok(BarIter { device: self, max_bars, index: Some(0), _phantom: PhantomData })
    }
    /// Checks if the device exists at all.
    fn exists<P: Platform>(&self) -> Result<bool, &'static str> {
        let (vendor_id, _) = self.vendor_device_id::<P>()?;
        Ok(vendor_id != 0xFFFF && vendor_id != 0x0000)
    }

    #[inline]
    pub fn bus(&self) -> u8 {
        (self.0 >> 8) as u8
    }

    #[inline]
    pub fn device(&self) -> u8 {
        ((self.0 >> 3) & 0b11111) as u8
    }

    #[inline]
    pub fn function(&self) -> u8 {
        (self.0 & 0b111) as u8
    }

    /// Returns the first function on the next device on the bus.
    ///
    /// Returns None if this is the last device on this device.
    pub fn next_device(&self) -> Option<Self> {
        let addr = Self((self.0 + (1 << 3)) & !0b111);
        if addr.bus() != self.bus() {
            None
        } else {
            Some(addr)
        }
    }

    /// Returns the next function on the bus, crossing to the next device if
    /// needed.
    ///
    /// Returns None if this is the last function on this bus.
    pub fn next(&self) -> Option<Self> {
        let addr = Self(self.0 + 1);
        if addr.bus() != self.bus() {
            None
        } else {
            Some(addr)
        }
    }
}

impl Display for PciAddress {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:02x}:{:02x}.{:x}", self.bus(), self.device(), self.function())
    }
}

impl TryFrom<(u8, u8, u8)> for PciAddress {
    type Error = &'static str;

    fn try_from((bus, device, function): (u8, u8, u8)) -> Result<Self, Self::Error> {
        PciAddress::new(bus, device, function)
    }
}

impl From<PciAddress> for u16 {
    fn from(value: PciAddress) -> Self {
        value.0
    }
}

/// Uses the legacy port-based IO method to read a u32 from the PCI
/// configuration space.
fn pci_read_cam<P: Platform>(address: &PciAddress, offset: u8) -> Result<u32, &'static str> {
    let port_factory = P::port_factory();
    let mut address_port: Port<u32> = port_factory.new_writer(PCI_PORT_CONFIGURATION_SPACE_ADDRESS);
    let mut data_port: Port<u32> = port_factory.new_reader(PCI_PORT_CONFIGURATION_SPACE_DATA);

    // Address register implemented per Section 3.2.2.3.2 of PCI spec, Rev 3.0.
    let value = (1u32 << 31) | ((Into::<u16>::into(*address) as u32) << 8) | ((offset as u32) << 2);
    // Safety: PCI_PORT_CONFIGURATION_SPACE_ADDRESS is a well-known port and should
    // be safe to write to even if we don't have a PCI bus.
    unsafe { address_port.try_write(value) }?;
    // Safety: PCI_PORT_CONFIGURATION_SPACE_DATA is a well-known port and should
    // be safe to read from even if we don't have a PCI bus (it'll return
    // 0xFFFFFFFF)
    unsafe { data_port.try_read() }
}

#[allow(dead_code)]
fn pci_write_cam<P: Platform>(
    address: &PciAddress,
    offset: u8,
    value: u32,
) -> Result<(), &'static str> {
    let port_factory = P::port_factory();
    let mut address_port: Port<u32> = port_factory.new_writer(PCI_PORT_CONFIGURATION_SPACE_ADDRESS);
    let mut data_port: Port<u32> = port_factory.new_reader(PCI_PORT_CONFIGURATION_SPACE_DATA);

    // Address register implemented per Section 3.2.2.3.2 of PCI spec, Rev 3.0.
    let address =
        (1u32 << 31) | ((Into::<u16>::into(*address) as u32) << 8) | ((offset as u32) << 2);
    // Safety: PCI_PORT_CONFIGURATION_SPACE_ADDRESS is a well-known port and should
    // be safe to write to even if we don't have a PCI bus.
    unsafe { address_port.try_write(address) }?;
    // Safety: PCI_PORT_CONFIGURATION_SPACE_DATA is a well-known port and should
    // be safe to write to even if we don't have a PCI bus.
    unsafe { data_port.try_write(value) }
}

struct BusDeviceIterator<P: Platform> {
    address: Option<PciAddress>,
    _phantom: PhantomData<P>,
}

impl<P: Platform> Iterator for BusDeviceIterator<P> {
    type Item = PciAddress;

    fn next(&mut self) -> Option<Self::Item> {
        // Shortcircuit if we've exhausted the bus.
        let current_address = self.address?;

        // Shortcut: if we know we're on a single-function device, step over to the next
        // device.
        self.address = if current_address.is_multi_function_device::<P>().unwrap() {
            current_address.next()
        } else {
            current_address.next_device()
        };

        // Ensure said next device actually exists.
        while let Some(address) = self.address {
            // Does the device exist?
            if address.exists::<P>().unwrap() {
                // Yes, it does.
                break;
            }
            // No; skip to the next function.
            // For future: can we skip all the functions and skip to the next device if
            // function() == 0? Inside a multi-function device there can be
            // gaps, but we'll need to read from the spec if function 0 is
            // always assumed to exist in multi-function devices.
            self.address = address.next();
        }

        Some(current_address)
    }
}

trait ResourceAllocatorIdx: Add<Output = Self> + PartialOrd + Sized + Clone + Copy {
    fn next_multiple_of(self, rhs: Self) -> Self;
}

impl ResourceAllocatorIdx for u16 {
    fn next_multiple_of(self, rhs: Self) -> Self {
        self.next_multiple_of(rhs)
    }
}

impl ResourceAllocatorIdx for u32 {
    fn next_multiple_of(self, rhs: Self) -> Self {
        self.next_multiple_of(rhs)
    }
}

impl ResourceAllocatorIdx for u64 {
    fn next_multiple_of(self, rhs: Self) -> Self {
        self.next_multiple_of(rhs)
    }
}

struct ResourceAllocator<Idx: ResourceAllocatorIdx> {
    range: Range<Idx>,
    index: Idx,
}

impl<Idx: ResourceAllocatorIdx> ResourceAllocator<Idx> {
    pub fn new(range: Range<Idx>) -> Self {
        let index = range.start;
        Self { range, index }
    }

    pub fn allocate(&mut self, size: Idx) -> Option<Range<Idx>> {
        // Ensure alignment with `size`.
        let index = self.index.next_multiple_of(size);
        if index + size > self.range.end {
            None
        } else {
            let result = index..index + size;
            self.index = index + size;
            Some(result)
        }
    }
}

struct PciBus {
    pub root: PciAddress,
}

impl PciBus {
    fn new<P: Platform>(bus: u8) -> Result<Option<Self>, &'static str> {
        let root = PciAddress::new(bus, 0, 0)?;
        if root.exists::<P>()? {
            Ok(Some(Self { root }))
        } else {
            Ok(None)
        }
    }

    fn init<P: Platform>(&mut self, windows: &PciWindows) -> Result<(), &'static str> {
        // Prepare the allocators for all the resources.
        let mut io_allocator = ResourceAllocator::new(windows.pci_window_16.clone());
        let mut mem32_allocator = ResourceAllocator::new(windows.pci_window_32.clone());
        let mut mem64_allocator = ResourceAllocator::new(windows.pci_window_64.clone());

        for function in self.iter_devices::<P>() {
            let (vendor_id, device_id) = function.vendor_device_id::<P>()?;
            let (class, subclass) = function.class_code::<P>()?;

            log::debug!(
                "Found PCI device: {}, {:04x}:{:04x}, class: {}{}",
                function,
                vendor_id,
                device_id,
                class,
                subclass
            );

            if class == PciClass::BRIDGE && subclass == PciSubclass::PCI_TO_PCI_BRIDGE {
                let bridge_bus_numbers = function.bridge_bus_numbers::<P>()?;
                log::debug!("PCI to PCI bridge:  {:?}", bridge_bus_numbers);
                log::warn!(
                    "UNIMPLEMENTED: leaving PCI bridge unconfigured, file a bug if you see this!"
                );
            }

            for bar in function.iter_bars::<P>()? {
                match bar {
                    PciBar::Memory32(address, bar) => {
                        log::debug!("  BAR{}: memory, size {}", bar.offset, bar.bar_size);
                        let allocation = mem32_allocator
                            .allocate(bar.bar_size)
                            .ok_or("out of memory for 32-bit memory BAR")?
                            .start;
                        log::debug!(
                            "    assigning [{:08x}-{:08x})",
                            allocation,
                            allocation + bar.bar_size
                        );
                        pci_write_cam::<P>(address, 0x4 + bar.offset, allocation)?;
                    }
                    PciBar::Memory64(address, bar) => {
                        log::debug!(
                            "  BAR{}: memory, 64-bit pref, size {}",
                            bar.offset,
                            bar.bar_size
                        );
                        let allocation = mem64_allocator
                            .allocate(bar.bar_size)
                            .ok_or("out of memory for 64-bit memory BAR")?
                            .start;
                        log::debug!(
                            "    assigning [{:016x}-{:016x})",
                            allocation,
                            allocation + bar.bar_size
                        );
                        pci_write_cam::<P>(
                            address,
                            0x4 + bar.offset,
                            (allocation & 0xFFFF_FFFF) as u32,
                        )?;
                        pci_write_cam::<P>(
                            address,
                            0x4 + bar.offset + 1,
                            (allocation >> 32) as u32,
                        )?;
                    }
                    PciBar::Io(address, bar) => {
                        log::debug!("  BAR{}: I/O, size {}", bar.offset, bar.bar_size);
                        let bar_size = bar.bar_size.try_into().unwrap();
                        let allocation = io_allocator
                            .allocate(bar_size)
                            .ok_or("out of memory for 64-bit memory BAR")?
                            .start;
                        log::debug!(
                            "    assigning [{:04x}-{:04x})",
                            allocation,
                            allocation + bar_size
                        );
                        pci_write_cam::<P>(address, 0x4 + bar.offset, allocation as u32 & !0b11)?;
                    }
                }
            }
        }
        Ok(())
    }

    fn iter_devices<P: Platform>(&self) -> BusDeviceIterator<P> {
        // We cheat a bit; the `new()` will never error as (any u8, 0, 0) is always
        // valid as an address. However, as we need a `Option` for the iterator, it's a
        // convenient way to make the types work instead of unwrapping.
        BusDeviceIterator { address: Some(self.root), _phantom: PhantomData }
    }
}

/// Location of the PCI resources on this machine.
#[derive(Debug)]
pub struct PciWindows {
    pub pci_window_16: Range<u16>,
    // These are still memory addresses, but we use u32 here as they must be in 32-bit memory.
    pub pci_window_32: Range<u32>,
    pub pci_window_64: Range<u64>,
}

trait Machine {
    const PCI_VENDOR_ID: u16;
    const PCI_DEVICE_ID: u16;

    fn io_port_range(
        _firmware: &mut dyn Firmware,
        _zero_page: &ZeroPage,
    ) -> Result<Range<u16>, &'static str> {
        // 16-bit I/O port ranges.
        // According to SeaBIOS here:
        // https://github.com/qemu/seabios/blob/b686f4600792c504f01929f761be473e298de33d/src/fw/pciinit.c#L1009
        // there are two common port ranges, depending on how many I/O assignments we
        // will need.
        //
        // For now, hard-code the (smaller) range of 0xc000 + 0x4000.

        Ok(0xc000..0xffff)
    }

    fn mmio32_hole(
        firmware: &mut dyn Firmware,
        zero_page: &ZeroPage,
    ) -> Result<Range<u32>, &'static str>;

    fn mmio64_hole<P: Platform>(
        firmware: &mut dyn Firmware,
        zero_page: &ZeroPage,
    ) -> Result<Range<u64>, &'static str>;
}

// How much memory to reserve for the 64-bit PCI hole. This is a fairly
// conservative 32 GiB.
const MMIO64_HOLE_SIZE: usize = 0x8_0000_0000;

struct I440fx {}

impl Machine for I440fx {
    const PCI_VENDOR_ID: u16 = 0x8086;
    const PCI_DEVICE_ID: u16 = 0x1237;

    fn mmio32_hole(
        firmware: &mut dyn Firmware,
        zero_page: &ZeroPage,
    ) -> Result<Range<u32>, &'static str> {
        let mut mmio32_hole_base = firmware
            .find(PCI_MMIO32_HOLE_BASE_FILE_NAME)
            .and_then(|file| {
                // The VMM is providing us the start of the hole.
                if file.size() > core::mem::size_of::<u64>() {
                    return None;
                }
                let mut hole: u64 = 0;
                // reading can fail, so now we will have an Option<Result> so that we can
                // propagate the error
                Some(firmware.read_file(&file, hole.as_mut_bytes()).and_then(|_| {
                    hole.try_into().map_err(|_| "VMM reported MMIO hole did not fit in u32")
                }))
            })
            .unwrap_or_else(|| {
                // No base from the VMM. Try to guess reasonable defaults; for this we look if
                // some well-known memory addresses are backed by real RAM or not. If not,
                // that's where we guess the hole will be.
                //
                // This mirrors what SeaBIOS is doing:
                // https://github.com/coreboot/seabios/blob/b686f4600792c504f01929f761be473e298de33d/src/fw/pciinit.c#L470
                // In EDK2, the magic happens here:
                // https://github.com/tianocore/edk2/blob/b58ce4c226768ced972bd49886e20c5ae6dfd8f0/OvmfPkg/Library/PlatformInitLib/Platform.c#L186
                // with `Uc32Base` determined here:
                // https://github.com/tianocore/edk2/blob/b58ce4c226768ced972bd49886e20c5ae6dfd8f0/OvmfPkg/Library/PlatformInitLib/MemDetect.c#L84
                //
                // SeaBIOS/EDK2 keep track of the "low" and "high" memory separately. We don't,
                // but we have a full e820 map to check whether the addresses are backed by real
                // memory or not.
                if zero_page.find_e820_entry(0x8000_0000).is_none() {
                    return Ok(0x8000_0000);
                }
                if zero_page.find_e820_entry(0xC000_0000).is_none() {
                    return Ok(0xC000_0000);
                }
                // We have no idea where the hole should go :(
                Err("could not find memory region for 32-bit PCI MMIO hole")
            })?;

        if let Some(file) = firmware.find(MMCFG_MEM_RESERVATION_FILE)
            && file.size() <= core::mem::size_of::<u64>()
        {
            let mut should_reserve: u64 = 0;
            firmware.read_file(&file, should_reserve.as_mut_bytes())?;
            if should_reserve == 1 {
                // Bump the base by 256 MoB
                mmio32_hole_base += 0x10000000;
            }
        }

        // EDK2 code:
        // https://github.com/tianocore/edk2/blob/b58ce4c226768ced972bd49886e20c5ae6dfd8f0/OvmfPkg/Library/PlatformInitLib/Platform.c#L187 (defined ad 0xFC00_0000)
        // SeaBIOS code:
        // https://github.com/coreboot/seabios/blob/b686f4600792c504f01929f761be473e298de33d/src/fw/pciinit.c#L51 (defined at 0xFEC0_0000)
        // For now we choose the lower of the two.
        let mmio32_hole_end = 0xFC00_0000;

        Ok(mmio32_hole_base..mmio32_hole_end)
    }

    fn mmio64_hole<P: Platform>(
        firmware: &mut dyn Firmware,
        zero_page: &ZeroPage,
    ) -> Result<Range<u64>, &'static str> {
        // It is possible for the host to provide PCI bridge address information in a
        // fw_cfg file, `etc/hardware-info`. EDK2 supports that mechanism, but I don't
        // see that mechanism being used in any the VMMs that immediately interest us.
        // Thus, let's kick that particular can down the road until we encounter a VMM
        // that requires us to support that mechanism.
        // But we should still print a warning if that file exists so that it wouldn't
        // come as a complete surprise.
        if firmware.find(c"etc/hardware-info").is_some() {
            log::warn!("your VMM exposes `etc/hardware-info`; stage0 currently does not support parsing that file and will ignore it!");
        }

        // EDK2 places the 64-bit hole at (2^(physmem_bits-3)..2^physmem_bits) (unless
        // otherwise instructed):
        //
        // https://github.com/tianocore/edk2/blob/d46aa46c8361194521391aa581593e556c707c6e/OvmfPkg/Library/PlatformInitLib/MemDetect.c#L796
        //
        // After which it moves it down if there is a conflict:
        //
        // https://github.com/tianocore/edk2/blob/d46aa46c8361194521391aa581593e556c707c6e/OvmfPkg/Library/PlatformInitLib/MemDetect.c#L809
        //
        // This is known as the "dynamic MMIO window".
        //
        // Otherwise, the window size is at least 32 GB (look for `PcdPciMmio64Size` in
        // the dsc files), the "classic MMIO window".
        //
        // SeaBIOS prefers to place the window somewhere around 512 GiB..1024 GiB mark:
        // BUILD_PCIMEM64_START = 0x80_0000_0000 (512 GB mark)
        // BUILD_PCIMEM64_END = 0x100_0000_0000 (1024 GB mark)
        // These are the build time defaults. But also see:
        // https://github.com/coreboot/seabios/blob/b686f4600792c504f01929f761be473e298de33d/src/fw/pciinit.c#L1138
        // https://github.com/coreboot/seabios/blob/b686f4600792c504f01929f761be473e298de33d/src/fw/pciinit.c#L1157
        //
        // Let's make some simplifying assumptions and try to fit a 32 GiB window
        // somewhere at the top of the available physical memory. You'd hope we can just
        // assume (at least) 48 bits available, but no.

        // We've now run into a VM where CPUID reports 48 bits of physical address
        // space, but the VMM is only backing it with 41.6 bits of address space, and we
        // place the MMIO range outside of what the VMM supports.
        //
        // Oops.
        //
        // We'll have to come back to this and figure out how to see through the VMM's
        // lies, but for now, let's lie and say 40 bits. This will break if the VM has
        // more than ~800 GiB of memory.
        let addr_size = 40;
        //let addr_size = P::guest_phys_addr_size();
        let top_of_memory: u64 = 1 << addr_size;
        // We'll also be relatively conservative and try to get away with just reserving
        // 32 GiB for the hole.

        // The hole should be aligned to 1G addresses. With enough bits, that should be
        // vacuously true, but just in case let's ensure that the top_of_memory is a
        // multiple of the hole size.
        let top_of_memory = align_down(top_of_memory, MMIO64_HOLE_SIZE as u64) as usize;

        // Let's start by sticking it at the very end of the address space.
        let mut mmio64_hole = top_of_memory - MMIO64_HOLE_SIZE..top_of_memory;

        // Keep scaling down until we find a hole or run out of memory.
        // In theory we could scale down by 1G chunks until we get to the 4G boundary,
        // but there should be enough address space available to use bigger, hole-sized
        // chunks.
        while !zero_page.check_e820_gap(mmio64_hole.clone())
            && mmio64_hole.start >= MMIO64_HOLE_SIZE
        {
            mmio64_hole.start -= MMIO64_HOLE_SIZE;
            mmio64_hole.end -= MMIO64_HOLE_SIZE;
        }

        if mmio64_hole.start < MMIO64_HOLE_SIZE {
            Err("could not find memory region for 64-bit PCI MMIO hole")
        } else {
            Ok(mmio64_hole.start as u64..mmio64_hole.end as u64)
        }
    }
}

struct Q35 {}

impl Machine for Q35 {
    const PCI_VENDOR_ID: u16 = 0x8086;
    const PCI_DEVICE_ID: u16 = 0x29C0;

    fn mmio32_hole(
        _firmware: &mut dyn Firmware,
        _zero_page: &ZeroPage,
    ) -> Result<Range<u32>, &'static str> {
        // SeaBIOS: PCI EXBAR start is hardcoded to 0xB000_0000 and size is 256 MiB:
        // https://github.com/coreboot/seabios/blob/b686f4600792c504f01929f761be473e298de33d/src/fw/dev-q35.h#L11
        // The PCI memory starts just past that (at 0xC000_0000, the 3G mark).
        // PCI memory end is hardcoded, same constant as with 440fx above.
        //
        // EDK2:
        // Uc32Base and Uc32Size determined here:
        // https://github.com/tianocore/edk2/blob/b58ce4c226768ced972bd49886e20c5ae6dfd8f0/OvmfPkg/Library/PlatformInitLib/MemDetect.c#L84
        // PCIe base address fixed at build to 0xE000_0000:
        // https://github.com/tianocore/edk2/blob/8d984e6a5742220d2b28bd85121000136d820fcb/OvmfPkg/OvmfPkgX64.dsc#L646
        //
        // Interestingly enough this means that the PCI MMIO and MMCONFIG regions are in
        // effect flipped for SeaBIOS and EDK2.

        // SeaBIOS memory layout (starts at 2.75 GiB):
        // [0xB000_0000, 0xC000_0000) - 256 MiB, PCI EXBAR
        // [0xC000_0000, 0xFC00_0000) - 960 MiB, PCI MMIO
        // [0xFC00_0000, 0xFFFF_FFFF) -  64 MiB, IO-APIC, HPET, LAPIC etc
        //
        // EDK2 memory layout:
        // [Uc32Base, 0xE000_0000) - PCI MMIO
        // [0xE000_0000, 0xF000_0000) - 256 MiB, MMCONFIG
        // [0xF000_0000, 0xFC00_0000) - 192 MiB, unused
        // [0xFC00_0000, 0xFFFF_FFFF) -  64 MiB, IO-APIC, HPET, LAPIC etc

        // For now we choose a hybrid approach. PCI MMIO will start at 0xB000_0000, the
        // 3G mark. This should always be unused with QEMU.
        let mmio32_hole_start = 0xB000_0000;
        // The end will be at 0xE000_0000, similar to EDK2. We will put MMCONFIG after
        // that, similar to EDK2. This leaves 768 MiB for the PCI MMIO memory.
        let mmio32_hole_end = 0xE000_0000;

        Ok(mmio32_hole_start..mmio32_hole_end)
    }

    fn mmio64_hole<P: Platform>(
        firmware: &mut dyn Firmware,
        zero_page: &ZeroPage,
    ) -> Result<Range<u64>, &'static str> {
        // No special treatment here.
        I440fx::mmio64_hole::<P>(firmware, zero_page)
    }
}

fn init_machine<P: Platform, M: Machine>(
    mut root_bus: PciBus,
    firmware: &mut dyn Firmware,
    zero_page: &mut ZeroPage,
) -> Result<Option<PciWindows>, &'static str> {
    // Determine the PCI holes. How this is done is unfortunately extremely clunky
    // and machine-specific.
    let pci_windows = PciWindows {
        pci_window_16: M::io_port_range(firmware, zero_page)?,
        pci_window_32: M::mmio32_hole(firmware, zero_page)?,
        pci_window_64: M::mmio64_hole::<P>(firmware, zero_page)?,
    };

    log::info!("PCI: using windows {:?}", pci_windows);

    root_bus.init::<P>(&pci_windows)?;

    // Find out if there are any extra roots.
    let extra_roots = read_extra_roots(firmware)?;
    if extra_roots > 0 {
        log::debug!("{} extra root buses reported by VMM", extra_roots);
    }
    Ok(Some(pci_windows))
}

pub fn init<P: Platform>(
    firmware: &mut dyn Firmware,
    zero_page: &mut ZeroPage,
) -> Result<Option<PciWindows>, &'static str> {
    // At this point we know nothing about the platform we're on, so we have to
    // rely on the legacy CAM to get the device ID of the first PCI root to
    // help us figure out on what kind of machine we are running.
    let root_bus = match PciBus::new::<P>(0)? {
        Some(bus) => bus,
        None => return Ok(None),
    };

    match root_bus.root.vendor_device_id::<P>()? {
        (I440fx::PCI_VENDOR_ID, I440fx::PCI_DEVICE_ID) => {
            init_machine::<P, I440fx>(root_bus, firmware, zero_page)
        }
        (Q35::PCI_VENDOR_ID, Q35::PCI_DEVICE_ID) => {
            init_machine::<P, Q35>(root_bus, firmware, zero_page)
        }
        (vendor_id, device_id) => {
            log::error!(
                "Unknown PCI root device: {:04x}:{:04x} -- will not initialize PCI bus",
                vendor_id,
                device_id
            );
            Ok(None)
        }
    }
}

fn read_extra_roots(firmware: &mut dyn Firmware) -> Result<u64, &'static str> {
    if let Some(file) = firmware.find(EXTRA_ROOTS_FILE_NAME) {
        if file.size() > core::mem::size_of::<u64>() {
            return Ok(0);
        }
        let mut roots: u64 = 0;
        firmware.read_file(&file, roots.as_mut_bytes())?;
        return Ok(roots);
    }

    // File not found, no extra roots.
    Ok(0)
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
    use oak_linux_boot_params::{BootE820Entry, E820EntryType};

    use super::*;
    use crate::hal::MockPlatform;

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

    #[googletest::test]
    fn pc_hole_from_fwcfg() {
        let mut firmware = TestFirmware::default();
        let zero_page = ZeroPage::new();

        firmware.files.insert(
            PCI_MMIO32_HOLE_BASE_FILE_NAME.to_owned(),
            Box::new(0x1234_0000u64.to_le_bytes()),
        );

        // We don't really test for the end right now; as long as it's after the start,
        // we're fine.
        assert_that!(
            I440fx::mmio32_hole(&mut firmware, &zero_page),
            ok(all!(field!(&Range.start, 0x1234_0000), field!(&Range.end, gt(0x1234_0000))))
        );
    }

    #[googletest::test]
    fn pc_hole_from_low_memory() {
        let mut firmware = TestFirmware::default();
        let mut zero_page = ZeroPage::new();
        // 32 MiB of memory. Welcome to the 90s!
        zero_page.insert_e820_entry(BootE820Entry::new(0x0, 0x200_0000, E820EntryType::RAM));
        // the hole should be at the 2 GiB mark
        assert_that!(
            I440fx::mmio32_hole(&mut firmware, &zero_page),
            ok(all!(field!(&Range.start, 0x8000_0000), field!(&Range.end, gt(0x8000_0000))))
        );
    }

    #[googletest::test]
    fn pc_hole_from_high_memory() {
        let mut firmware = TestFirmware::default();
        let mut zero_page = ZeroPage::new();
        // 2.5 GiB of memory. Welcome to the 00s! This guarantees we cover the 2GiB
        // mark, but don't fill the full 3G space.
        zero_page.insert_e820_entry(BootE820Entry::new(0x0, 0xA000_0000, E820EntryType::RAM));
        // the hole should now be at 3 GiB mark
        assert_that!(
            I440fx::mmio32_hole(&mut firmware, &zero_page),
            ok(all!(field!(&Range.start, 0xC000_0000), field!(&Range.end, gt(0xC000_0000))))
        );
    }

    #[googletest::test]
    fn q35_hole() {
        // Not much to test, besides there being a hole.
        let mut firmware = TestFirmware::default();
        let zero_page = ZeroPage::new();
        assert_that!(
            Q35::mmio32_hole(&mut firmware, &zero_page),
            ok(all!(
                field!(&Range.start, gt(0x8000_0000)), // higher than 2 GiB
                field!(&Range.end, le(0xFE00_0000))    // less than the reserved location
            ))
        )
    }

    #[googletest::test]
    fn mmio64_hole() {
        let gpa_bits = 40;

        // This sets global state for MockPlatform, so beware! However, I don't think
        // we'll ever need different values in other tests.
        let ctx = MockPlatform::guest_phys_addr_size_context();
        ctx.expect().returning(move || gpa_bits);

        let mut firmware = TestFirmware::default();
        let mut zero_page = ZeroPage::new();
        let hole = I440fx::mmio64_hole::<MockPlatform>(&mut firmware, &zero_page);

        // We didn't reserve any memory, so the hole should be right at the very top.
        assert_that!(
            hole,
            ok(all!(
                field!(&Range.start, le(1 << gpa_bits)),
                field!(&Range.end, eq(1 << gpa_bits))
            ))
        );

        // 1 GB at the very top is reserved. The hole should have moved down.
        zero_page.insert_e820_entry(BootE820Entry::new(
            (1 << gpa_bits) - 0x4000_0000,
            0x4000_0000,
            E820EntryType::RAM,
        ));
        let hole = I440fx::mmio64_hole::<MockPlatform>(&mut firmware, &zero_page);
        assert_that!(
            hole,
            ok(all!(
                field!(&Range.start, le((1 << gpa_bits) - 0x4000_0000)),
                field!(&Range.end, le((1 << gpa_bits) - 0x4000_0000))
            ))
        );

        // There is no address space available. How did you get such a machine?
        zero_page.insert_e820_entry(BootE820Entry::new(
            0,
            (1 << gpa_bits) - 0x4000_0000,
            E820EntryType::RAM,
        ));
        let hole = I440fx::mmio64_hole::<MockPlatform>(&mut firmware, &zero_page);
        assert_that!(hole, err(anything()));

        // Okay, _fine_, there is a hole. But it's too small.
        let mut zero_page = ZeroPage::new();
        zero_page.insert_e820_entry(BootE820Entry::new(0, MMIO64_HOLE_SIZE, E820EntryType::RAM));
        zero_page.insert_e820_entry(BootE820Entry::new(
            MMIO64_HOLE_SIZE + (MMIO64_HOLE_SIZE / 2),
            (1 << gpa_bits) - MMIO64_HOLE_SIZE - (MMIO64_HOLE_SIZE / 2),
            E820EntryType::RAM,
        ));
        let hole = I440fx::mmio64_hole::<MockPlatform>(&mut firmware, &zero_page);
        assert_that!(hole, err(anything()));

        // There is an exactly perfect hole.
        let mut zero_page = ZeroPage::new();
        zero_page.insert_e820_entry(BootE820Entry::new(0, MMIO64_HOLE_SIZE, E820EntryType::RAM));
        zero_page.insert_e820_entry(BootE820Entry::new(
            MMIO64_HOLE_SIZE + MMIO64_HOLE_SIZE,
            (1 << gpa_bits) - MMIO64_HOLE_SIZE - MMIO64_HOLE_SIZE,
            E820EntryType::RAM,
        ));
        let hole = I440fx::mmio64_hole::<MockPlatform>(&mut firmware, &zero_page);
        assert_that!(
            hole,
            ok(all!(
                field!(&Range.start, eq(MMIO64_HOLE_SIZE as u64)),
                field!(&Range.end, eq((MMIO64_HOLE_SIZE + MMIO64_HOLE_SIZE) as u64))
            ))
        );
    }

    #[googletest::test]
    fn test_resource_allocator() {
        let mut allocator = ResourceAllocator::new(16u32..128u32);
        assert_that!(allocator.allocate(16), some(eq(&(16..32))));
        assert_that!(allocator.allocate(64), some(eq(&(64..128))));
        assert_that!(allocator.allocate(16), none());
    }
}
