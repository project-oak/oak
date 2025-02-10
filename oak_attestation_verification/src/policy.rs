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

pub mod application;
pub mod binary;
pub mod container;
pub mod firmware;
pub mod kernel;
pub mod platform;
pub mod system;

/// Public key used by the client to establish an HPKE session with the enclave.
pub const ENCRYPTION_PUBLIC_KEY_NAME: &str = "oak-encryption-public-key:X25519";
/// Public key used to verify artifacts signed by the enclave.
pub const SIGNING_PUBLIC_KEY_NAME: &str = "oak-signing-public-key:ecdsa-p256";
/// Public key used to verify that the Noise handshake transcript signature.
pub const SESSION_BINDING_PUBLIC_KEY_NAME: &str = "oak-session-binding-public-key:ecdsa-p256";
