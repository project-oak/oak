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

#[no_mangle]
pub static HANDSHAKE_TYPE_NOISE_KK: u32 = 1;
#[no_mangle]
pub static HANDSHAKE_TYPE_NOISE_KN: u32 = 2;
#[no_mangle]
pub static HANDSHAKE_TYPE_NOISE_NK: u32 = 3;
#[no_mangle]
pub static HANDSHAKE_TYPE_NOISE_NN: u32 = 4;

#[no_mangle]
pub static ATTESTATION_TYPE_BIDIRECTIONAL: u32 = 1;
#[no_mangle]
pub static ATTESTATION_TYPE_SELF_UNIDIRECTIONAL: u32 = 2;
#[no_mangle]
pub static ATTESTATION_TYPE_PEER_UNIDIRECTIONAL: u32 = 3;
#[no_mangle]
pub static ATTESTATION_TYPE_UNATTESTED: u32 = 4;

use oak_session::{
    attestation::AttestationType,
    config::{SessionConfig, SessionConfigBuilder},
    handshake::HandshakeType,
};
use oak_session_ffi_types::Error;

/// Create a new `SessionConfigBuilder` for use in FFI;
#[no_mangle]
pub extern "C" fn new_session_config_builder(
    attestation_type: u32,
    handshake_type: u32,
) -> ErrorOrSessionConfigBuilder {
    let attestation_type = match attestation_type {
        x if x == ATTESTATION_TYPE_BIDIRECTIONAL => AttestationType::Bidirectional,
        x if x == ATTESTATION_TYPE_SELF_UNIDIRECTIONAL => AttestationType::SelfUnidirectional,
        x if x == ATTESTATION_TYPE_PEER_UNIDIRECTIONAL => AttestationType::PeerUnidirectional,
        x if x == ATTESTATION_TYPE_UNATTESTED => AttestationType::Unattested,
        _ => {
            return ErrorOrSessionConfigBuilder::err(
                "Unknown attestation type value {attestation_type}",
            )
        }
    };
    let handshake_type = match handshake_type {
        x if x == HANDSHAKE_TYPE_NOISE_KK => HandshakeType::NoiseKK,
        x if x == HANDSHAKE_TYPE_NOISE_KN => HandshakeType::NoiseKN,
        x if x == HANDSHAKE_TYPE_NOISE_NK => HandshakeType::NoiseNK,
        x if x == HANDSHAKE_TYPE_NOISE_NN => HandshakeType::NoiseNN,
        _ => {
            return ErrorOrSessionConfigBuilder::err(
                "Unknown handshake type value {handshake_type}",
            )
        }
    };
    let session_config_builder = SessionConfig::builder(attestation_type, handshake_type);
    ErrorOrSessionConfigBuilder::ok(Box::into_raw(Box::new(session_config_builder)))
}

/// Consumes and builds the config for the provided builder.
/// The returned SessionConfig pointer is still owned by Rust.
///
/// When passing it as a constructor argument to new_client_session or
/// new_server_session, ownership of the object will be returned fully to Rust,
/// and it should not be used on the C++ side anymore.
///
/// # Safety
///
/// builder is a valid, properly aligned pointer to a SessionConfigBuilder.
#[no_mangle]
pub unsafe extern "C" fn session_config_builder_build(
    builder: *mut SessionConfigBuilder,
) -> *mut SessionConfig {
    // Take back ownership.
    let builder = Box::from_raw(builder);
    Box::into_raw(Box::new(builder.build()))
}

#[repr(C)]
pub struct ErrorOrSessionConfigBuilder {
    pub result: *mut SessionConfigBuilder,
    pub error: *const Error,
}

impl ErrorOrSessionConfigBuilder {
    fn ok(result: *mut SessionConfigBuilder) -> Self {
        Self { result, error: std::ptr::null() }
    }

    fn err(message: impl AsRef<str>) -> Self {
        Self { result: std::ptr::null_mut(), error: Error::new_raw(message) }
    }
}
