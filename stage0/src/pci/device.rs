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

use core::fmt::Display;

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

#[cfg(test)]
mod tests {
    use googletest::{description::Description, matcher::MatcherResult, prelude::*};

    use super::*;

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
}
