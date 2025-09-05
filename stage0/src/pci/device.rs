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

use alloc::{boxed::Box, rc::Rc};
use core::fmt::Display;

use spinning_top::Spinlock;
use strum::FromRepr;

use crate::pci::config_access::ConfigAccess;

/// Address of a PCI function, in the bus-device-function format.
///
/// The BDF address is used to uniquely identify devices and functions on the
/// PCI(e) bus.
///
/// Each bus can have up to 32 devices, and each device up to 8 functions.
///
/// Basic structure: BBBBBBBBDDDDDFFF
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct Bdf(u16);

impl Bdf {
    pub const fn new(bus: u8, device: u8, function: u8) -> Result<Self, &'static str> {
        if device > 0b11111 {
            return Err("invalid device number");
        }
        if function > 0b111 {
            return Err("invalid function number");
        }

        Ok(Self((bus as u16) << 8 | (device as u16) << 3 | (function as u16)))
    }

    /// Returns the PCI address for the root bridge, `00:00.0`.`
    pub const fn root() -> Self {
        Self(0)
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
        let addr = Self(self.0.checked_add(1 << 3)? & !0b111);
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
        let addr = Self(self.0.checked_add(1)?);
        if addr.bus() != self.bus() {
            None
        } else {
            Some(addr)
        }
    }
}

impl Display for Bdf {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:02x}:{:02x}.{:x}", self.bus(), self.device(), self.function())
    }
}

impl TryFrom<(u8, u8, u8)> for Bdf {
    type Error = &'static str;

    fn try_from((bus, device, function): (u8, u8, u8)) -> Result<Self, Self::Error> {
        Bdf::new(bus, device, function)
    }
}

impl From<Bdf> for u16 {
    fn from(value: Bdf) -> Self {
        value.0
    }
}

/// PCI class codes.
///
/// We use a struct instead of enum because Rust enums are closed, but we will
/// not give an exhaustive list of class codes.
///
/// See the PCI Code and ID Assignment Specification on pcisig.com for the
/// authoritative source.
#[derive(PartialEq, Eq)]
#[repr(transparent)]
pub struct PciClass(pub u8);

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
pub struct PciSubclass(pub u8);
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

#[derive(Debug, Clone)]
pub struct PciFunction {
    bdf: Bdf,
}

impl PciFunction {
    pub fn new(bdf: Bdf, access: &mut dyn ConfigAccess) -> Result<Option<Self>, &'static str> {
        let func = Self { bdf };

        if func.exists(access)? {
            Ok(Some(func))
        } else {
            Ok(None)
        }
    }

    /// Returns the Vendor ID and Device ID for the address.
    pub fn vendor_device_id(
        &self,
        access: &mut dyn ConfigAccess,
    ) -> Result<(u16, u16), &'static str> {
        // Register 0x00: Device ID, Vendor ID (16b each)
        let value = access.read(self.bdf, 0x00)?;
        Ok(((value & 0xFFFF) as u16, (value >> 16) as u16))
    }

    pub fn class_code(
        &self,
        access: &mut dyn ConfigAccess,
    ) -> Result<(PciClass, PciSubclass), &'static str> {
        // Register 0x02: Class Code, Subclass, Prog IF, Revision ID (8b each)
        let value = access.read(self.bdf, 0x02)?;
        Ok((PciClass((value >> 24) as u8), PciSubclass((value >> 16) as u8)))
    }

    fn exists(&self, access: &mut dyn ConfigAccess) -> Result<bool, &'static str> {
        let (vendor_id, _) = self.vendor_device_id(access)?;
        Ok(vendor_id != 0xFFFF && vendor_id != 0x0000)
    }

    pub fn iter_bars(
        &self,
        access: Rc<Spinlock<Box<dyn ConfigAccess>>>,
    ) -> Result<BarIter, &'static str> {
        let (class, subclass) = self.class_code(access.lock().as_mut())?;
        let max_bars = if class == PciClass::BRIDGE && subclass == PciSubclass::PCI_TO_PCI_BRIDGE {
            2
        } else {
            6
        };
        Ok(BarIter { bdf: self.bdf, max_bars, index: Some(0), access })
    }
}

pub struct BarIter {
    bdf: Bdf,
    // Bridges have up to 2 BARs, normal devices 6.
    max_bars: u8,
    index: Option<u8>,
    access: Rc<Spinlock<Box<dyn ConfigAccess>>>,
}

impl core::fmt::Debug for BarIter {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("BarIter")
            .field("bdf", &self.bdf)
            .field("max_bars", &self.max_bars)
            .field("index", &self.index)
            .finish_non_exhaustive()
    }
}

impl Iterator for BarIter {
    type Item = PciBar;

    fn next(&mut self) -> Option<Self::Item> {
        // Try to find a next BAR.
        loop {
            self.index = self.index.filter(|&index| index < self.max_bars);
            let index = self.index?;

            let bar = PciBar::new(self.bdf, index, self.access.lock().as_mut()).ok()?;
            // We've consumed at least one entry.
            let _ = self.index.insert(index + 1);
            match bar {
                None => {
                    // Unimplemented BAR.
                    continue;
                }
                Some(PciBar::Io { .. }) | Some(PciBar::Memory32 { .. }) => {
                    return bar;
                }
                Some(PciBar::Memory64 { .. }) => {
                    // 64-bit memory BARs take two slots.
                    let _ = self.index.insert(index + 2);
                    return bar;
                }
            }
        }
    }
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

#[allow(dead_code)]
#[derive(Debug, PartialEq)]
pub enum PciBar {
    Memory32 { bdf: Bdf, offset: u8, prefetchable: bool, bar_size: u32 },
    Memory64 { bdf: Bdf, offset: u8, prefetchable: bool, bar_size: u64 },
    Io { bdf: Bdf, offset: u8, bar_size: u32 },
}

impl PciBar {
    const BAR_REGISTER_OFFSET: u8 = 0x4;

    pub fn new(
        bdf: Bdf,
        offset: u8,
        access: &mut dyn ConfigAccess,
    ) -> Result<Option<Self>, &'static str> {
        // Proble the BAR by writing all-ones.

        access.write(bdf, Self::BAR_REGISTER_OFFSET + offset, 0xFFFF_FFFF)?;
        let value = access.read(bdf, Self::BAR_REGISTER_OFFSET + offset)?;

        if value == 0 {
            // Unimplemented BAR.
            return Ok(None);
        }

        // We have a valid BAR. I/O and 32-bit memory BARs take one slot,
        // 64-bit memory BARs two slots.
        let bar_type = PciBarKind::from_repr(value & PciBarKind::MASK).ok_or("invalid BAR")?;

        Ok(match bar_type {
            PciBarKind::Memory => {
                let size = PciMemoryBarSize::from_repr(value & PciMemoryBarSize::MASK)
                    .ok_or("invalid BAR")?;
                let prefetchable = value & 0b1000 != 0;
                // Mask away all but the BAR size field.
                let value = value & !0b1111;

                if size == PciMemoryBarSize::Size64 {
                    // For 64-bit BARs, we need to read the next register as well.
                    access.write(bdf, Self::BAR_REGISTER_OFFSET + offset + 1, 0xFFFF_FFFF)?;
                    let upper_half =
                        access.read(bdf, Self::BAR_REGISTER_OFFSET + offset + 1)? as u64;

                    Some(PciBar::Memory64 {
                        bdf,
                        offset,
                        prefetchable,
                        bar_size: !((upper_half << 32) + (value as u64)) + 1,
                    })
                } else {
                    Some(PciBar::Memory32 { bdf, offset, prefetchable, bar_size: !value + 1 })
                }
            }
            PciBarKind::Io => {
                let value = value & !PciBarKind::MASK;
                Some(PciBar::Io { bdf, offset, bar_size: !value + 1 })
            }
        })
    }

    pub fn set_address(
        &mut self,
        address: u64,
        access: &mut dyn ConfigAccess,
    ) -> Result<(), &'static str> {
        match self {
            PciBar::Memory32 { bdf, offset, .. } => {
                let address: u32 = address.try_into().map_err(|_| "invalid address")?;
                access.write(*bdf, Self::BAR_REGISTER_OFFSET + *offset, address & !0b1111)
            }
            PciBar::Memory64 { bdf, offset, .. } => {
                access.write(
                    *bdf,
                    Self::BAR_REGISTER_OFFSET + *offset,
                    (address & 0xFFFF_FFFF) as u32 & !0b1111,
                )?;
                access.write(*bdf, Self::BAR_REGISTER_OFFSET + *offset + 1, (address >> 32) as u32)
            }
            PciBar::Io { bdf, offset, .. } => {
                let address: u32 = address.try_into().map_err(|_| "invalid address")?;
                access.write(*bdf, Self::BAR_REGISTER_OFFSET + *offset, address & !0b11)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use googletest::{description::Description, matcher::MatcherResult, prelude::*};
    use mockall::predicate::eq as mockall_eq;

    use super::*;
    use crate::pci::config_access::MockConfigAccess;

    #[derive(MatcherBase)]
    struct BdfMatcher<BusMatcher, DeviceMatcher, FunctionMatcher> {
        bus_matcher: BusMatcher,
        device_matcher: DeviceMatcher,
        function_matcher: FunctionMatcher,
    }
    impl<BusMatcher: Matcher<u8>, DeviceMatcher: Matcher<u8>, FunctionMatcher: Matcher<u8>>
        Matcher<Bdf> for BdfMatcher<BusMatcher, DeviceMatcher, FunctionMatcher>
    {
        fn matches(&self, actual: Bdf) -> MatcherResult {
            if self.bus_matcher.matches(actual.bus()).is_no_match() {
                return MatcherResult::NoMatch;
            }
            if self.device_matcher.matches(actual.device()).is_no_match() {
                return MatcherResult::NoMatch;
            }
            if self.function_matcher.matches(actual.function()).is_no_match() {
                return MatcherResult::NoMatch;
            }

            MatcherResult::Match
        }

        fn describe(&self, matcher_result: MatcherResult) -> Description {
            Description::new()
                .text(match matcher_result {
                    MatcherResult::Match => "is a BDF with",
                    MatcherResult::NoMatch => "is not a BDF with",
                })
                .collect([
                    Description::new()
                        .text("bus")
                        .nested(self.bus_matcher.describe(MatcherResult::Match)),
                    Description::new()
                        .text("device")
                        .nested(self.device_matcher.describe(MatcherResult::Match)),
                    Description::new()
                        .text("function")
                        .nested(self.function_matcher.describe(MatcherResult::Match)),
                ])
        }

        fn explain_match(&self, actual: Bdf) -> Description {
            Description::new().text("is a BDF with").collect([
                Description::new().text("bus").nested(self.bus_matcher.explain_match(actual.bus())),
                Description::new()
                    .text("device")
                    .nested(self.device_matcher.explain_match(actual.device())),
                Description::new()
                    .text("function")
                    .nested(self.function_matcher.explain_match(actual.function())),
            ])
        }
    }

    fn bdf<BusMatcher, DeviceMatcher, FunctionMatcher>(
        bus_matcher: BusMatcher,
        device_matcher: DeviceMatcher,
        function_matcher: FunctionMatcher,
    ) -> BdfMatcher<BusMatcher, DeviceMatcher, FunctionMatcher> {
        BdfMatcher { bus_matcher, device_matcher, function_matcher }
    }

    #[test]
    fn test_new_bdf() {
        assert_that!(
            Bdf::new(0, 0, 0),
            ok(all!(displays_as(eq("00:00.0")), eq(Bdf::root()), bdf(eq(0), eq(0), eq(0))))
        );
        assert_that!(
            Bdf::new(0, 31, 0),
            ok(all!(displays_as(eq("00:1f.0")), bdf(eq(0), eq(31), eq(0))))
        );
        assert_that!(
            Bdf::new(0, 31, 7),
            ok(all!(displays_as(eq("00:1f.7")), bdf(eq(0), eq(31), eq(7))))
        );
        assert_that!(
            Bdf::new(255, 31, 7),
            ok(all!(displays_as(eq("ff:1f.7")), bdf(eq(255), eq(31), eq(7))))
        );
        assert_that!(Bdf::new(0, 32, 0), err(anything()));
        assert_that!(Bdf::new(0, 31, 8), err(anything()));
    }

    #[test]
    fn test_bdf_increment() {
        assert_that!(Bdf::new(0, 0, 0).unwrap().next(), some(eq(Bdf::new(0, 0, 1).unwrap())));
        assert_that!(Bdf::new(0, 0, 7).unwrap().next(), some(eq(Bdf::new(0, 1, 0).unwrap())));
        assert_that!(
            Bdf::new(0, 0, 0).unwrap().next_device(),
            some(eq(Bdf::new(0, 1, 0).unwrap()))
        );
        assert_that!(
            Bdf::new(0, 0, 7).unwrap().next_device(),
            some(eq(Bdf::new(0, 1, 0).unwrap()))
        );
        assert_that!(Bdf::new(255, 31, 7).unwrap().next(), none());
        assert_that!(Bdf::new(255, 31, 0).unwrap().next_device(), none());
        assert_that!(Bdf::new(255, 31, 7).unwrap().next_device(), none());
    }

    #[test]
    fn test_unimplemented_bar() {
        let bdf = Bdf::new(1, 2, 3).unwrap();
        let mut access = MockConfigAccess::new();
        access
            .expect_write()
            .with(mockall_eq(bdf), mockall_eq(PciBar::BAR_REGISTER_OFFSET), mockall_eq(0xFFFF_FFFF))
            .return_const(Ok(()));
        access
            .expect_read()
            .with(mockall_eq(bdf), mockall_eq(PciBar::BAR_REGISTER_OFFSET))
            .return_const(Ok(0));
        assert_that!(PciBar::new(bdf, 0, &mut access), ok(none()));
    }

    #[test]
    fn test_32bit_memory_bar() {
        let mut access = MockConfigAccess::new();
        access.expect_write().return_const(Ok(()));
        // 32-bit, non-prefetchable, memory BAR of size 256 bytes.
        access
            .expect_read()
            .with(mockall_eq(Bdf::root()), mockall_eq(PciBar::BAR_REGISTER_OFFSET + 2))
            .return_const(Ok(0xFFFF_FF00));
        let bar = PciBar::new(Bdf::root(), 2, &mut access);

        assert_that!(
            bar,
            ok(some(matches_pattern!(PciBar::Memory32 {
                bdf: eq(&Bdf::root()),
                offset: eq(&2),
                prefetchable: eq(&false),
                bar_size: eq(&256)
            })))
        );
    }

    #[test]
    fn test_64bit_memory_bar() {
        let mut access = MockConfigAccess::new();
        access.expect_write().return_const(Ok(()));
        // 64-bit, prefetchable, memory BAR of size 65536 bytes.
        access
            .expect_read()
            .with(mockall_eq(Bdf::root()), mockall_eq(PciBar::BAR_REGISTER_OFFSET))
            .return_const(Ok(0xFFFF_000C));
        access
            .expect_read()
            .with(mockall_eq(Bdf::root()), mockall_eq(PciBar::BAR_REGISTER_OFFSET + 1))
            .return_const(Ok(0xFFFF_FFFF));
        let bar = PciBar::new(Bdf::root(), 0, &mut access);

        assert_that!(
            bar,
            ok(some(matches_pattern!(PciBar::Memory64 {
                bdf: eq(&Bdf::root()),
                offset: eq(&0),
                prefetchable: eq(&true),
                bar_size: eq(&65536)
            })))
        );
    }

    #[test]
    fn test_io_bar() {
        let mut access = MockConfigAccess::new();
        access.expect_write().return_const(Ok(()));
        // I/O BAR of size 4 bytes.
        access.expect_read().return_const(Ok(0xFFFF_FFFD));
        let bar = PciBar::new(Bdf::root(), 0, &mut access);

        assert_that!(
            bar,
            ok(some(matches_pattern!(PciBar::Io {
                bdf: eq(&Bdf::root()),
                offset: eq(&0),
                bar_size: eq(&4)
            })))
        );
    }

    #[test]
    fn test_set_address_32bit_memory_bar() {
        let mut access = MockConfigAccess::new();
        let mut bar =
            PciBar::Memory32 { bdf: Bdf::root(), offset: 1, prefetchable: false, bar_size: 256 };
        access
            .expect_write()
            .with(
                mockall_eq(Bdf::root()),
                mockall_eq(PciBar::BAR_REGISTER_OFFSET + 1),
                mockall_eq(0x1000_0000),
            )
            .return_const(Ok(()));

        assert_that!(bar.set_address(0x1000_0000, &mut access), ok(eq(())));
    }

    #[test]
    fn test_set_address_64bit_memory_bar() {
        let mut access = MockConfigAccess::new();
        let mut bar =
            PciBar::Memory64 { bdf: Bdf::root(), offset: 0, prefetchable: false, bar_size: 65536 };
        access
            .expect_write()
            .with(
                mockall_eq(Bdf::root()),
                mockall_eq(PciBar::BAR_REGISTER_OFFSET),
                mockall_eq(0x1000_0000),
            )
            .return_const(Ok(()));
        access
            .expect_write()
            .with(
                mockall_eq(Bdf::root()),
                mockall_eq(PciBar::BAR_REGISTER_OFFSET + 1),
                mockall_eq(0x2),
            )
            .return_const(Ok(()));

        assert_that!(bar.set_address(0x2_1000_0000, &mut access), ok(eq(())));
    }

    #[test]
    fn test_set_address_io_bar() {
        let mut access = MockConfigAccess::new();
        let mut bar = PciBar::Io { bdf: Bdf::root(), offset: 0, bar_size: 4 };
        access
            .expect_write()
            .with(
                mockall_eq(Bdf::root()),
                mockall_eq(PciBar::BAR_REGISTER_OFFSET),
                mockall_eq(0x1000),
            )
            .return_const(Ok(()));
        assert_that!(bar.set_address(0x1000, &mut access), ok(eq(())));
    }

    #[test]
    fn test_pci_function_new() {
        let mut access = MockConfigAccess::new();
        access.expect_read().return_const(Ok(0x4242_1022));
        assert_that!(PciFunction::new(Bdf::root(), &mut access), ok(some(anything())));
    }

    #[test]
    fn test_pci_function_new_not_found() {
        let mut access = MockConfigAccess::new();
        access.expect_read().return_const(Ok(0xFFFF_FFFF));
        assert_that!(PciFunction::new(Bdf::root(), &mut access), ok(none()));
    }

    #[test]
    fn test_bar_iter_regular_device() {
        let mut access = MockConfigAccess::new();
        // Not a bridge device.
        access.expect_read().with(mockall_eq(Bdf::root()), mockall_eq(2)).return_const(Ok(0));
        let access = Rc::new(Spinlock::new(Box::new(access) as Box<dyn ConfigAccess>));
        let func = PciFunction { bdf: Bdf::root() };

        assert_that!(func.iter_bars(access.clone()), ok(anything()));
        assert_that!(func.iter_bars(access).unwrap().max_bars, eq(6));
    }

    #[test]
    fn test_bar_iter_bridge() {
        let mut access = MockConfigAccess::new();
        // PCI-to-PCI bridge.
        access
            .expect_read()
            .with(mockall_eq(Bdf::root()), mockall_eq(2))
            .return_const(Ok(0x0604_0000));
        let access = Rc::new(Spinlock::new(Box::new(access) as Box<dyn ConfigAccess>));
        let func = PciFunction { bdf: Bdf::root() };

        assert_that!(func.iter_bars(access.clone()), ok(anything()));
        assert_that!(func.iter_bars(access).unwrap().max_bars, eq(2));
    }

    #[test]
    fn test_bar_iteration() {
        let mut access = MockConfigAccess::new();

        // --- Expectations for PciFunction::new() ---
        access
            .expect_read()
            .with(mockall_eq(Bdf::root()), mockall_eq(0x00))
            .return_const(Ok(0x1234_5678));

        // --- Expectations for iter_bars() ---
        // Class code for a generic device, not a bridge.
        access.expect_read().with(mockall_eq(Bdf::root()), mockall_eq(0x02)).return_const(Ok(0));

        // --- Expectations for the iterator ---
        // BAR 0: 32-bit memory BAR, 256 bytes
        access
            .expect_write()
            .with(mockall_eq(Bdf::root()), mockall_eq(0x04), mockall_eq(0xFFFF_FFFF))
            .return_const(Ok(()));
        access
            .expect_read()
            .with(mockall_eq(Bdf::root()), mockall_eq(0x04))
            .return_const(Ok(0xFFFF_FF00));

        // BAR 1: 64-bit memory BAR, 65536 bytes (consumes BAR 2 as well)
        access
            .expect_write()
            .with(mockall_eq(Bdf::root()), mockall_eq(0x05), mockall_eq(0xFFFF_FFFF))
            .return_const(Ok(()));
        access
            .expect_read()
            .with(mockall_eq(Bdf::root()), mockall_eq(0x05))
            .return_const(Ok(0xFFFF_000C));
        access
            .expect_write()
            .with(mockall_eq(Bdf::root()), mockall_eq(0x06), mockall_eq(0xFFFF_FFFF))
            .return_const(Ok(()));
        access
            .expect_read()
            .with(mockall_eq(Bdf::root()), mockall_eq(0x06))
            .return_const(Ok(0xFFFF_FFFF));

        // BAR 3: I/O BAR, 4 bytes
        access
            .expect_write()
            .with(mockall_eq(Bdf::root()), mockall_eq(0x07), mockall_eq(0xFFFF_FFFF))
            .return_const(Ok(()));
        access
            .expect_read()
            .with(mockall_eq(Bdf::root()), mockall_eq(0x07))
            .return_const(Ok(0xFFFF_FFFD));

        // BAR 4: Unimplemented
        access
            .expect_write()
            .with(mockall_eq(Bdf::root()), mockall_eq(0x08), mockall_eq(0xFFFF_FFFF))
            .return_const(Ok(()));
        access.expect_read().with(mockall_eq(Bdf::root()), mockall_eq(0x08)).return_const(Ok(0));

        // BAR 5: 32-bit memory BAR, 1024 bytes
        access
            .expect_write()
            .with(mockall_eq(Bdf::root()), mockall_eq(0x09), mockall_eq(0xFFFF_FFFF))
            .return_const(Ok(()));
        access
            .expect_read()
            .with(mockall_eq(Bdf::root()), mockall_eq(0x09))
            .return_const(Ok(0xFFFF_FC00));

        // --- Execution ---
        let func = PciFunction::new(Bdf::root(), &mut access).unwrap().unwrap();
        let access_rc = Rc::new(Spinlock::new(Box::new(access) as Box<dyn ConfigAccess>));
        let bars: Vec<PciBar> = func.iter_bars(access_rc).unwrap().collect();

        // --- Assertions ---
        assert_that!(
            bars,
            elements_are![
                matches_pattern!(PciBar::Memory32 { offset: eq(&0), bar_size: eq(&256), .. }),
                matches_pattern!(PciBar::Memory64 { offset: eq(&1), bar_size: eq(&65536), .. }),
                matches_pattern!(PciBar::Io { offset: eq(&3), bar_size: eq(&4), .. }),
                matches_pattern!(PciBar::Memory32 { offset: eq(&5), bar_size: eq(&1024), .. })
            ]
        );
    }
}
