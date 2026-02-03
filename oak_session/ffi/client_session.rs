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

use oak_ffi_bytes::BytesView;
use oak_ffi_error::{Error, ErrorOrRustBytes};
use oak_proto_rust::oak::{
    attestation::v1::CollectedAttestation,
    session::v1::{PlaintextMessage, SessionResponse},
};
use oak_session::{
    ProtocolEngine,
    config::SessionConfig,
    session::{ClientSession, Session},
};
use prost::Message;

/// Create a new [`ClientSession`] instance for FFI usage.
///
/// Ownership of the proivded `SessionConfig` object will be passed back to Rust
/// and it will be freed.
///
/// If the functions succeeds,
/// `ErrorOrClientSession::result` will contain a pointer to the
/// [`ClientSession`] that can be used as the first argument to the other FFI
/// calls.
///
/// In case of an error, `ErrorOrClientSession::error` will contain a poiner to
/// an error, containing a string description of the Rust error encountered.
/// The error should be freed with `oak_session_ffi_types::free_error`.
///
/// When the instance is no longer needed, it should be released with
/// [`free_client_session`].
///
/// # Safety
///
/// config is a valid, properly aligned pointer to a SessionConfig object. Once
/// the config object has been provided here, it should not be used again.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn new_client_session(config: *mut SessionConfig) -> ErrorOrClientSession {
    let config = unsafe { Box::from_raw(config) };
    let client_session = ClientSession::create(*config);
    match client_session {
        Ok(session) => ErrorOrClientSession {
            result: Box::into_raw(Box::new(session)),
            error: std::ptr::null(),
        },
        Err(e) => ErrorOrClientSession { result: std::ptr::null_mut(), error: Error::new_raw(e) },
    }
}

/// Calls [`ClientSession::is_open`] on the provided `ClientSession`
///
/// # Safety
///
/// The provided [`ClientSession`] pointer should be non-null, properly aligned,
/// and points to a valid [`ClientSession`] instance.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn client_is_open(session: *const ClientSession) -> bool {
    unsafe { (*session).is_open() }
}

/// Calls [`ClientSession::get_outgoing_message`] on the provided
/// [`ClientSession`] pointer.
///
/// If the call results in an error, the `error` field of the result will be
/// populated with a string decription of the Rust error.
///
/// If non-null bytes are returned, they should be freed with free_bytes.
/// If a non-null error is returned, it should be freed with free_error.
///
/// # Safety
///
/// The provided [`ClientSession`] pointer should be non-null, properly aligned,
/// and points to a valid [`ClientSession`] instance.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn client_get_outgoing_message(
    session: *mut ClientSession,
) -> ErrorOrRustBytes {
    safe_client_get_outgoing_message(unsafe { &mut *session })
}

fn safe_client_get_outgoing_message(session: &mut ClientSession) -> ErrorOrRustBytes {
    let outgoing_message = match session.get_outgoing_message() {
        Ok(Some(om)) => om,
        Ok(None) => return ErrorOrRustBytes::null(),
        Err(e) => return ErrorOrRustBytes::err(e),
    };

    ErrorOrRustBytes::ok(Message::encode_to_vec(&outgoing_message).into_boxed_slice())
}

/// Calls [`ClientSession:put_incoming_message`] on the provided pointer.
//
/// If the call results in an error, a non-null error containing a string
/// descripton of the Rust error will be returned.
///
/// If a non-null error is returned, it should be freed with free_error.
///
/// # Safety
///
/// * The provided [`ClientSession`] pointer should be non-null, properly
///   aligned, and points to a valid [`ClientSession`] instance.
///
/// * The provided [`BytesView`] is valid.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn client_put_incoming_message(
    session: *mut ClientSession,
    session_response_bytes: BytesView,
) -> *const Error {
    safe_client_put_incoming_message(unsafe { &mut *session }, unsafe {
        session_response_bytes.as_slice()
    })
}

fn safe_client_put_incoming_message(
    session: &mut ClientSession,
    session_response_slice: &[u8],
) -> *const Error {
    let session_response = match SessionResponse::decode(session_response_slice) {
        Ok(r) => r,
        Err(e) => return Error::new_raw(e),
    };

    let result = session.put_incoming_message(session_response);

    match result {
        Ok(_) => std::ptr::null(),
        Err(e) => Error::new_raw(e),
    }
}

/// Calls [`ClientSession::read`] on the provided  pointer.
///
/// If the call results in an error, the `error` field of the result will be
/// populated with a string decription of the Rust error.
///
/// The returned [`RustBytes`] will be the bytes in the `plaintext` field of the
/// [`PlaintextMessage`] returned by the state machine.
/// We make this divergence from the underlying Rust API to
/// avoid the copy/serialization/deserialization overhead associated with
/// passing the proto back and forth.
///
/// If non-null bytes are returned, they should be freed with free_bytes.
/// If a non-null error is returned, it should be freed with free_error.
///
/// # Safety
///
/// The provided [`ClientSession`] pointer should be non-null, properly aligned,
/// and points to a valid [`ClientSession`] instance.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn client_read(session: *mut ClientSession) -> ErrorOrRustBytes {
    safe_client_read(unsafe { &mut *session })
}

fn safe_client_read(session: &mut ClientSession) -> ErrorOrRustBytes {
    let decrypted_message = match session.read() {
        Ok(Some(om)) => om,
        Ok(None) => return ErrorOrRustBytes::null(),
        Err(e) => return ErrorOrRustBytes::err(e),
    };

    ErrorOrRustBytes::ok(decrypted_message.plaintext.into_boxed_slice())
}

/// Calls [`ClientSession::write`] on the provided
/// [`ClientSession`] pointer.
///
/// The provided `RustBytes` should be the raw application bytes to be
/// encrypted. They'll be added to a `PlaintextMessage` proto by the library
/// implementation. We make this divergence from the underlying Rust API to
/// avoid the copy/serialization/deserialization overhead associated with
/// passing the proto back and forth.
///
/// If the call results in an error, the `error` field of the result will be
/// populated with a string decription of the Rust error.
///
/// If a non-null error is returned, it should be freed with free_error.
///
/// # Safety
///
/// * The provided [`ClientSession`] pointer should be non-null, properly
///   aligned, and points to a valid [`ClientSession`] instance.
///
/// * The provided [`BytesView`] is valid.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn client_write(
    session: *mut ClientSession,
    plaintext_message_bytes: BytesView,
) -> *const Error {
    safe_client_write(unsafe { &mut *session }, unsafe { plaintext_message_bytes.as_slice() })
}

fn safe_client_write(session: &mut ClientSession, plaintext_bytes_slice: &[u8]) -> *const Error {
    match session.write(PlaintextMessage { plaintext: plaintext_bytes_slice.to_vec() }) {
        Ok(()) => std::ptr::null(),
        Err(e) => Error::new_raw(e),
    }
}

/// Calls [`ClientSession::get_session_binding_token`]
///
/// If non-null bytes are returned, they should be freed with free_bytes.
/// If a non-null error is returned, it should be freed with free_error.
///
/// # Safety
///
/// * The provided [`ClientSession`] pointer should be non-null, properly
///   aligned, and points to a valid [`ClientSession`] instance.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn client_get_session_binding_token(
    session: *mut ClientSession,
    info: BytesView,
) -> ErrorOrRustBytes {
    safe_client_get_session_binding_token(unsafe { &*session }, unsafe { info.as_slice() })
}

fn safe_client_get_session_binding_token(session: &ClientSession, info: &[u8]) -> ErrorOrRustBytes {
    match session.get_session_binding_token(info) {
        Ok(st) => ErrorOrRustBytes::ok(st.into_boxed_slice()),
        Err(e) => ErrorOrRustBytes::err(e),
    }
}

/// Calls [`ClientSession::get_peer_attestation_evidence`].
///
/// If the call results in an error, the `error` field of the result will be
/// populated with a string description of the Rust error.
///
/// The returned [`RustBytes`] will be the serialized `CollectedAttestation`
/// proto.
///
/// # Safety
///
/// The provided [`ClientSession`] pointer should be non-null, properly aligned,
/// and points to a valid [`ClientSession`] instance.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn client_get_peer_attestation_evidence(
    session: *const ClientSession,
) -> ErrorOrRustBytes {
    safe_client_get_peer_attestation_evidence(unsafe { &*session })
}

fn safe_client_get_peer_attestation_evidence(session: &ClientSession) -> ErrorOrRustBytes {
    match session.get_peer_attestation_evidence() {
        Ok(session_evidence) => {
            let proto_evidence = CollectedAttestation {
                endorsed_evidence: session_evidence.evidence,
                session_bindings: session_evidence.evidence_bindings,
                handshake_hash: session_evidence.handshake_hash,
                ..Default::default()
            };
            ErrorOrRustBytes::ok(Message::encode_to_vec(&proto_evidence).into_boxed_slice())
        }
        Err(e) => ErrorOrRustBytes::err(e),
    }
}

/// Return ownership of the [`ClientSession`] pointer to Rust, where it will be
/// dropped and all related memory released.
///
/// Every call to `new_client_session` should be paired with this call.
///
/// # Safety
///
/// * The provided [`ClientSession`] pointer should be non-null, properly
///   aligned, and points to a valid [`ClientSession`] instance.
///
/// * The pointer should not be used anymore after calling this function.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn free_client_session(session: *mut ClientSession) {
    unsafe {
        drop(Box::from_raw(session));
    }
}

#[repr(C)]
pub struct ErrorOrClientSession {
    pub result: *mut ClientSession,
    pub error: *const Error,
}
