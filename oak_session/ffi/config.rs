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

use std::ffi::{c_char, c_void};

use oak_attestation_types::{attester::Attester, endorser::Endorser};
use oak_attestation_verification_types::verifier::AttestationVerifier;
use oak_crypto::{
    identity_key::{IdentityKey, IdentityKeyHandle},
    noise_handshake::client::P256_SCALAR_LEN,
};
use oak_ffi_bytes::BytesView;
use oak_ffi_error::{Error, ErrorOrRustBytes};
use oak_proto_rust::attestation::{
    CERTIFICATE_BASED_ATTESTATION_ID_CSTR, CONFIDENTIAL_SPACE_ATTESTATION_ID_CSTR,
};
use oak_session::{
    attestation::AttestationType,
    config::{SessionConfig, SessionConfigBuilder},
    handshake::HandshakeType,
    session_binding::SignatureBinderBuilder,
};
use p256::ecdsa::SigningKey;

#[no_mangle]
pub extern "C" fn certificate_based_attestation_id() -> *const c_char {
    CERTIFICATE_BASED_ATTESTATION_ID_CSTR.as_ptr()
}

#[no_mangle]
pub extern "C" fn confidential_space_attestation_id() -> *const c_char {
    CONFIDENTIAL_SPACE_ATTESTATION_ID_CSTR.as_ptr()
}

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

/// A wrapper around a *mut c_void that holds a pointer to a `dyn Attester`
///
/// Attesters that are to be provided as `oak_session` configuration items in
/// C++ code should provide a constructor wrapper around the desired `Attester`
/// implementation that returns the pointer wrapped in this structure.
#[repr(C)]
pub struct FfiAttester {
    // Opaque dyn Attester
    attester: *mut c_void,
}

impl FfiAttester {
    pub fn new(attester: Box<dyn Attester>) -> Self {
        Self { attester: Box::into_raw(Box::new(attester)) as *mut c_void }
    }

    pub fn null() -> Self {
        Self { attester: std::ptr::null_mut() }
    }

    pub fn into_attester(self) -> Box<dyn Attester> {
        unsafe { *Box::from_raw(self.attester as *mut _) }
    }
}

/// A wrapper around a *mut c_void that holds a pointer to a `dyn Endorser`
///
/// Endorsers that are to be provided as `oak_session` configuration items in
/// C++ code should provide a constructor wrapper around the desired `Endorser`
/// implementation that returns the pointer wrapped in this structure.
#[repr(C)]
pub struct FfiEndorser {
    // Opaque dyn Endorser
    pub endorser: *mut c_void,
}

impl FfiEndorser {
    pub fn new(endorser: Box<dyn Endorser>) -> Self {
        Self { endorser: Box::into_raw(Box::new(endorser)) as *mut c_void }
    }

    pub fn null() -> Self {
        Self { endorser: std::ptr::null_mut() }
    }

    pub fn into_endorser(self) -> Box<dyn Endorser> {
        unsafe { *Box::from_raw(self.endorser as *mut _) }
    }
}

/// A wrapper around a *mut c_void that holds a pointer to a `dyn
/// AttestationVerifier`
///
/// AttestationVerifiers that are to be provided as `oak_session` configuration
/// items in C++ code should provide a constructor wrapper around the desired
/// `AttestationVerifier` implementation that returns the pointer wrapped in
/// this structure.
#[repr(C)]
pub struct FfiAttestationVerifier {
    // Opaque dyn AttestationVerifier
    pub verifier: *mut c_void,
}

impl FfiAttestationVerifier {
    pub fn new(verifier: Box<dyn AttestationVerifier>) -> Self {
        Self { verifier: Box::into_raw(Box::new(verifier)) as *mut c_void }
    }

    pub fn into_verifier(self) -> Box<dyn AttestationVerifier> {
        unsafe { *Box::from_raw(self.verifier as *mut _) }
    }
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

/// Consumes and releases the memory of the SessionConfig.
///
/// # Safety
///
/// session_config must be a valid, properly aligned pointer to a SessionConfig.
#[no_mangle]
pub unsafe extern "C" fn session_config_free(session_config: *mut SessionConfig) {
    drop(Box::from_raw(session_config));
}

/// Call add_self_attestion on the provided builder.
///
/// # Safety
///
/// * builder is a valid, properly aligned pointer to a SessionConfigBuilder.
/// * attester_id is a valid Bytes instances.
/// * FfiAttester was obtained from a suitable source and has not been used in
///   another call that consumes it.
#[no_mangle]
pub unsafe extern "C" fn session_config_builder_add_self_attester(
    builder: *mut SessionConfigBuilder,
    attester_id: BytesView,
    ffi_attester: FfiAttester,
) -> *mut SessionConfigBuilder {
    let attester: Box<dyn Attester> = ffi_attester.into_attester();
    let next_builder = Box::from_raw(builder)
        .add_self_attester(String::from_utf8_lossy(attester_id.as_slice()).to_string(), attester);
    Box::into_raw(Box::new(next_builder))
}

/// Call add_self_endorser on the provided builder.
///
/// # Safety
///
/// * builder is a valid, properly aligned pointer to a SessionConfigBuilder.
/// * endorser_id is a valid Bytes instances.
/// * FfiEndorser was obtained from a suitable source and has not been used in
///   another call that consumes it.
#[no_mangle]
pub unsafe extern "C" fn session_config_builder_add_self_endorser(
    builder: *mut SessionConfigBuilder,
    endorser_id: BytesView,
    ffi_endorser: FfiEndorser,
) -> *mut SessionConfigBuilder {
    let endorser: Box<dyn Endorser> = ffi_endorser.into_endorser();
    let next_builder = Box::from_raw(builder)
        .add_self_endorser(String::from_utf8_lossy(endorser_id.as_slice()).to_string(), endorser);
    Box::into_raw(Box::new(next_builder))
}

/// Call add_peer_verifier on the provided builder.
///
/// # Safety
///
/// * builder is a valid, properly aligned pointer to a SessionConfigBuilder.
/// * attester_id is a valid Bytes instances.
/// * FfiAttestationVerifier was obtained from a suitable source and has not
///   been used in another call that consumes it.
#[no_mangle]
pub unsafe extern "C" fn session_config_builder_add_peer_verifier(
    builder: *mut SessionConfigBuilder,
    attester_id: BytesView,
    ffi_verifier: FfiAttestationVerifier,
) -> *mut SessionConfigBuilder {
    let verifier: Box<dyn AttestationVerifier> = ffi_verifier.into_verifier();
    let next_builder = Box::from_raw(builder)
        .add_peer_verifier(String::from_utf8_lossy(attester_id.as_slice()).to_string(), verifier);
    Box::into_raw(Box::new(next_builder))
}

/// Call add_sesion_binder on the provided builder.
///
/// This call does not consume the SigningKey.
///
/// # Safety
///
/// * builder is a valid, properly aligned pointer to a SessionConfigBuilder.
/// * attester_id is a valid BytesView instances.
/// * binding_server_key was obtained from a suitable source and is still valid.
#[no_mangle]
pub unsafe extern "C" fn session_config_builder_add_session_binder(
    builder: *mut SessionConfigBuilder,
    attester_id: BytesView,
    binding_server_key: *const SigningKey,
) -> *mut SessionConfigBuilder {
    let signing_key = (*binding_server_key).clone();
    let next_builder = Box::from_raw(builder).add_session_binder(
        String::from_utf8_lossy(attester_id.as_slice()).to_string(),
        Box::new(SignatureBinderBuilder::default().signer(Box::new(signing_key)).build().unwrap()),
    );
    Box::into_raw(Box::new(next_builder))
}

/// Call set_peer_static_public_key on the provided builder.
///
/// # Safety
///
/// * builder is a valid, properly aligned pointer to a SessionConfigBuilder.
/// * public_key is a valid, properly aligned BytesView.
#[no_mangle]
pub unsafe extern "C" fn session_config_builder_set_peer_static_public_key(
    builder: *mut SessionConfigBuilder,
    public_key: BytesView,
) -> *mut SessionConfigBuilder {
    let next_builder = Box::from_raw(builder).set_peer_static_public_key(public_key.as_slice());
    Box::into_raw(Box::new(next_builder))
}

/// Call set_self_private_key on the provided builder.
///
/// This function consumes the provided IdentityKey, reclaiming ownership on the
/// Rust side.
///
/// # Safety
///
/// * builder is a valid, properly aligned pointer to a SessionConfigBuilder.
/// * identity is a valid, properly aligned, acquired from a suitable source.
#[no_mangle]
pub unsafe extern "C" fn session_config_builder_set_self_static_private_key(
    builder: *mut SessionConfigBuilder,
    identity_key_ptr: *mut IdentityKey,
) -> *mut SessionConfigBuilder {
    let identity_key = Box::from_raw(identity_key_ptr);
    let next_builder = Box::from_raw(builder).set_self_static_private_key(identity_key);
    Box::into_raw(Box::new(next_builder))
}

/// Create a new IdentityKey instance.
#[no_mangle]
pub extern "C" fn new_identity_key() -> *mut IdentityKey {
    Box::into_raw(Box::new(IdentityKey::generate()))
}

/// Create a new IdentityKey instance from the provided bytes.
///
/// If the functions succeeds,
/// `ErrorOrIdentity::result` will contain a pointer to the
/// [`IdentityKey`]. It should be freed by returning it to Rust via a function
/// call that reclaims ownership.
///
/// In case of an error, `ErrorOrIdentityKey::error` will contain a poiner to
/// an error, containing a string description of the Rust error encountered.
/// The error should be freed with `oak_session_ffi_types::free_error`.
///
/// # Safety
///
/// * bytes is a valid, properly aligned pointer to a SessionConfigBuilder.
#[no_mangle]
pub unsafe extern "C" fn new_identity_key_from_bytes(bytes: BytesView) -> ErrorOrIdentityKey {
    match <[u8; P256_SCALAR_LEN]>::try_from(bytes.as_slice()) {
        Ok(bytes) => {
            ErrorOrIdentityKey::ok(Box::into_raw(Box::new(IdentityKey::from_bytes(bytes))))
        }
        Err(e) => ErrorOrIdentityKey::err(e),
    }
}

/// Call get_public_key on the provided IdentityKey.
///
/// # Safety
///
/// * identity_key is valid, properly aligned, acquired from a suitable source.
#[no_mangle]
pub unsafe extern "C" fn identity_key_get_public_key(
    identity_key: *const IdentityKey,
) -> ErrorOrRustBytes {
    match (*identity_key).get_public_key() {
        Ok(ik) => ErrorOrRustBytes::ok(ik.into_boxed_slice()),
        Err(e) => ErrorOrRustBytes::err(e),
    }
}

#[repr(C)]
pub struct ErrorOrSessionConfigBuilder {
    pub result: *mut SessionConfigBuilder,
    pub error: *const Error,
}

impl ErrorOrSessionConfigBuilder {
    pub fn ok(result: *mut SessionConfigBuilder) -> Self {
        Self { result, error: std::ptr::null() }
    }

    pub fn err(message: impl std::fmt::Display) -> Self {
        Self { result: std::ptr::null_mut(), error: Error::new_raw(message) }
    }
}

#[repr(C)]
pub struct ErrorOrIdentityKey {
    pub result: *mut IdentityKey,
    pub error: *const Error,
}

impl ErrorOrIdentityKey {
    pub fn ok(result: *mut IdentityKey) -> Self {
        Self { result, error: std::ptr::null() }
    }

    pub fn err(message: impl std::fmt::Display) -> Self {
        Self { result: std::ptr::null_mut(), error: Error::new_raw(message) }
    }
}
