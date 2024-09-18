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

pub mod mmio;

use alloc::vec::Vec;
use core::arch::x86_64::{CpuidResult, __cpuid};

pub use mmio::*;
use oak_attestation::attester::{Attester, Serializable};
use oak_dice::evidence::TeePlatform;
use oak_linux_boot_params::BootE820Entry;
use oak_proto_rust::oak::attestation::v1::Evidence;
use oak_stage0_dice::DerivedKey;
use x86_64::{
    registers::model_specific::Msr,
    structures::{
        paging::{Page, PageSize, Size4KiB},
        port::{PortRead, PortWrite},
    },
};
use zerocopy::{AsBytes, FromBytes};

use super::{PageAssignment, PortFactory};
use crate::{paging::PageEncryption, zero_page::ZeroPage};

pub struct Base {}

/// An attester implementation that does nothing.
pub struct NoOpAttester;

impl Attester for NoOpAttester {
    fn extend(&mut self, _encoded_event: &[u8]) -> anyhow::Result<()> {
        Ok(())
    }

    fn quote(&self) -> anyhow::Result<Evidence> {
        anyhow::bail!("quoting is not supported")
    }
}

impl Serializable for NoOpAttester {
    fn deserialize(_bytes: &[u8]) -> anyhow::Result<Self> {
        Ok(NoOpAttester)
    }
    fn serialize(self) -> Vec<u8> {
        Vec::default()
    }
}

impl crate::Platform for Base {
    type Mmio<S: PageSize> = mmio::Mmio<S>;
    type Attester = NoOpAttester;

    fn cpuid(leaf: u32) -> CpuidResult {
        // Safety: all CPUs we care about are modern enough to support CPUID.
        unsafe { __cpuid(leaf) }
    }

    unsafe fn mmio<S: PageSize>(base_address: x86_64::PhysAddr) -> Self::Mmio<S> {
        mmio::Mmio::new(base_address)
    }

    fn port_factory() -> PortFactory {
        // Safety: all these function pointers are marked as unsafe, but you can't have
        // a unsafe closure.
        PortFactory {
            read_u8: |port| unsafe { Ok(u8::read_from_port(port)) },
            read_u16: |port| unsafe { Ok(u16::read_from_port(port)) },
            read_u32: |port| unsafe { Ok(u32::read_from_port(port)) },
            write_u8: |port, value| {
                unsafe { u8::write_to_port(port, value) };
                Ok(())
            },
            write_u16: |port, value| {
                unsafe { u16::write_to_port(port, value) };
                Ok(())
            },
            write_u32: |port, value| {
                unsafe { u32::write_to_port(port, value) };
                Ok(())
            },
        }
    }

    fn early_initialize_platform() {}

    fn prefill_e820_table<T: AsBytes + FromBytes>(_: &mut T) -> Result<usize, &'static str> {
        Err("not needed")
    }

    fn initialize_platform(_e820_table: &[BootE820Entry]) {}

    fn deinit_platform() {}

    fn populate_zero_page(_zero_page: &mut ZeroPage) {}

    fn get_attester() -> Result<Self::Attester, &'static str> {
        Ok(NoOpAttester {})
    }

    fn get_derived_key() -> Result<DerivedKey, &'static str> {
        oak_stage0_dice::mock_derived_key()
    }

    fn change_page_state(_page: Page<Size4KiB>, _state: PageAssignment) {}

    fn revalidate_page(_page: Page<Size4KiB>) {}

    fn page_table_mask(_encryption_state: PageEncryption) -> u64 {
        0
    }

    fn encrypted() -> u64 {
        0
    }

    fn tee_platform() -> TeePlatform {
        TeePlatform::None
    }

    unsafe fn read_msr(msr: u32) -> u64 {
        Msr::new(msr).read()
    }

    unsafe fn write_msr(msr: u32, value: u64) {
        Msr::new(msr).write(value)
    }
}
