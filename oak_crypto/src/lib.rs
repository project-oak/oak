//
// Copyright 2023 The Project Oak Authors
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

#![no_std]
#![feature(try_blocks)]

extern crate alloc;
extern crate static_assertions;

#[cfg(test)]
extern crate std;

pub mod certificate;
pub mod encryption_key;
pub mod encryptor;
pub mod hpke;
pub mod identity_key;
pub mod noise_handshake;
pub mod signer;
#[cfg(test)]
mod tests;
pub mod verifier;

pub const EMPTY_ASSOCIATED_DATA: &[u8] = b"";
