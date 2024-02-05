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

extern crate alloc;

pub mod channel;
pub mod instance_attestation;
#[cfg(any(feature = "mock_attestation", doc))]
#[doc(cfg(feature = "mock_attestation"))]
pub mod mock_attestation;
pub mod utils;
pub use oak_crypto::encryptor::EncryptionKeyHandle;
use oak_crypto::encryptor::EncryptionKeyProvider;
use oak_dice::evidence::Evidence;
/// Marks a function as the entrypoint to an enclave app and sets up an conviences such an
/// allocator, logger, panic handler.
///
/// This macro assumes that crates using it have declared the [`no_std`] and [`no_main`]
/// attributes, and enabled the [`alloc_error_handler`] unstable feature of the rust compiler.
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

/// Exposes the ability to sign bytestrings using a private key that has been endorsed in
/// the Attestation Evidence.
pub trait Signer {
    /// Attempt to sign the provided message bytestring using a signing private key, a
    /// corresponding public key of which is contained in the Attestation Evidence.
    fn sign(&self, message: &[u8]) -> anyhow::Result<oak_crypto::signer::Signature>;
}

/// Exposes the ability to read the Attestation Evidence.
/// Note: Applications should only use the evidence to initially send it to the host application
/// once, which then sends it to the clients. It is discouraged for enclave applications to operate
/// directly with evidences.
pub trait EvidenceProvider {
    fn get_evidence(&self) -> &Evidence;
}

/// Wrapper for DICE evidence and application private keys.
pub(crate) struct DiceWrapper {
    pub evidence: Evidence,
    pub encryption_key: EncryptionKeyProvider,
    pub signing_key: p256::ecdsa::SigningKey,
}
