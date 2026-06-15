//
// Copyright 2026 The Project Oak Authors
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

//! Intel Trust Domain Extensions (TDX) support for the Oak Restricted Kernel.
//!
//! This crate provides the implementation of the hardware abstraction layer
//! (HAL) traits for Intel TDX. It implements the [`oak_hal::Platform`] and
//! [`oak_hal::MsrAccess`] traits, as well as
//! [`oak_restricted_kernel::hal::KernelPlatform`], allowing the Oak Restricted
//! Kernel to run inside an Intel TDX Trust Domain (TD).
//!
//! # Architecture
//!
//! Interaction with the TDX module and the host hypervisor is performed via VM
//! calls and TD calls. These are wrapped by the `oak_tdx_guest` crate, which
//! this crate relies upon to:
//! - Interact with CPUID via TDVMCALLs.
//! - Set up MMIO access via `TdxMmio` (which implements `oak_hal::Mmio` using
//!   TDVMCALLs).
//! - Set up Port I/O factory.
//! - Manage page assignment state via TDVMCALLs to change memory from private
//!   to shared and vice versa.
//! - Accept pages dynamically using TDG.MEM.PAGE.ACCEPT.
//! - Handle Model Specific Register (MSR) access.
//! - Implement TDX memory encryption initialization and status checking.

#![no_std]

pub mod tdx;

pub use tdx::Tdx;
