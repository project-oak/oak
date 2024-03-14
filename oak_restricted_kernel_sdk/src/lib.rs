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

#![feature(doc_cfg)]
#![cfg_attr(not(test), no_std)]
#![feature(never_type)]
#![feature(unwrap_infallible)]

extern crate alloc;

pub mod attestation;
pub mod channel;
pub mod crypto;
#[cfg(any(feature = "mock_sdk", doc))]
#[doc(cfg(feature = "mock_sdk"))]
pub mod mock_sdk;
pub mod utils;
pub use oak_crypto::encryption_key::EncryptionKeyHandle;

/// Marks a function as the entrypoint to an enclave app and sets up an
/// conviences such an allocator, logger, panic handler.
///
/// This macro assumes that crates using it have declared the [`no_std`] and
/// [`no_main`] attributes, and enabled the [`alloc_error_handler`] unstable
/// feature of the rust compiler.
///
/// [`no_std`]: <https://github.com/rust-lang/rust/issues/51540>
/// [`no_main`]: <https://docs.rust-embedded.org/embedonomicon/smallest-no-std.html#the-code>
/// [`alloc_error_handler`]: <https://github.com/rust-lang/rust/issues/51540>
///
/// # Examples
///
/// Filename: src/main.rs
///
/// ```ignore
/// #![no_std]
/// #![no_main]
/// #![feature(alloc_error_handler)]
///
/// extern crate alloc;
///
/// use oak_restricted_kernel_sdk::entrypoint;
///
/// #[entrypoint]
/// fn start_enclave_app() -> ! {
///     // TODO(#0000): implement business logic below.
///     unimplemented!();
/// }
/// ```
pub use oak_restricted_kernel_sdk_proc_macro::entrypoint;
