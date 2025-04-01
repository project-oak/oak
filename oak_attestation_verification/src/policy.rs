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
pub mod application_keys;
pub mod binary;
pub mod container;
pub mod firmware;
pub mod kernel;
pub mod platform;
pub mod session_binding_public_key;
pub mod system;

/// Public key used to verify that the Noise handshake transcript signature.
pub const SESSION_BINDING_PUBLIC_KEY_ID: &str = "oak-session-binding-public-key:ecdsa-p256";
/// Key used to encrypt a single message with hybrid encryption before sending
/// it to the enclave.
pub const HYBRID_ENCRYPTION_PUBLIC_KEY_ID: &str = "oak-hybrid-encryption-public-key:X25519";
/// Key used to verify artifacts generated and signed by the enclave.
pub const SIGNING_PUBLIC_KEY_ID: &str = "oak-signing-public-key:ecdsa-p256";
