//
// Copyright 2024 The Project Oak Authors
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

mod mmio;

use core::arch::x86_64::{CpuidResult, __cpuid};

pub use mmio::*;
pub use oak_stage0_dice::{
    mock_attestation_report as get_attestation, mock_derived_key as get_derived_key,
};
pub use x86_64::registers::model_specific::Msr;
use x86_64::structures::{
    paging::PageSize,
    port::{PortRead, PortWrite},
};

pub struct Base {}

impl crate::Platform for Base {
    type Mmio<S: PageSize> = mmio::Mmio<S>;

    fn cpuid(leaf: u32) -> CpuidResult {
        // Safety: all CPUs we care about are modern enough to support CPUID.
        unsafe { __cpuid(leaf) }
    }

    unsafe fn mmio<S: PageSize>(base_address: x86_64::PhysAddr) -> Self::Mmio<S> {
        mmio::Mmio::new(base_address)
    }

    unsafe fn read_u8_from_port(port: u16) -> Result<u8, &'static str> {
        Ok(u8::read_from_port(port))
    }

    unsafe fn write_u8_to_port(port: u16, value: u8) -> Result<(), &'static str> {
        u8::write_to_port(port, value);
        Ok(())
    }

    unsafe fn read_u16_from_port(port: u16) -> Result<u16, &'static str> {
        Ok(u16::read_from_port(port))
    }

    unsafe fn write_u16_to_port(port: u16, value: u16) -> Result<(), &'static str> {
        u16::write_to_port(port, value);
        Ok(())
    }

    unsafe fn read_u32_from_port(port: u16) -> Result<u32, &'static str> {
        Ok(u32::read_from_port(port))
    }

    unsafe fn write_u32_to_port(port: u16, value: u32) -> Result<(), &'static str> {
        u32::write_to_port(port, value);
        Ok(())
    }
}
