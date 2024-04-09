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

//! Rust wrappers for instructions and structs for use by SNP-active guests to
//! manage page state and interact with the hypervisor and the secure processor.

#![no_std]

use x86_64::{PhysAddr, VirtAddr};

pub mod ap_jump_table;
pub mod cpuid;
#[cfg(feature = "rust-crypto")]
pub mod crypto;
pub mod ghcb;
pub mod guest;
pub mod instructions;
pub mod interrupts;
pub mod io;
pub mod msr;
pub mod secrets;
pub mod vmsa;

// TODO(#3394): Move to a shared crate.
/// Memory address translation functions.
pub trait Translator: Fn(VirtAddr) -> Option<PhysAddr> {}
impl<X: Fn(VirtAddr) -> Option<PhysAddr>> Translator for X {}
