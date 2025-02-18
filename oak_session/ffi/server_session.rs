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
use oak_proto_rust::oak::session::v1::{PlaintextMessage, SessionRequest};
use oak_session::{
    config::SessionConfig,
    session::{ServerSession, Session},
    ProtocolEngine,
};
use prost::Message;

///  Create a new [`ServerSession`] instance for FFI usage.
///
///  Ownership of the proivded `SessionConfig` object will be passed back to
///  Rust and it will be freed.
///
///  If the functions succeeds, `ErrorOrServerSession::result` will contain a
///  pointer to the [`ServerSession`] that can be used as the first argument to
///  the other `server_*`` FFI calls.
///
///  In case of an error, `ErrorOrServerSession::error` will contain a poiner to
///  an error, containing a string description of the Rust error encountered.
///  The error should be freed with `oak_session_ffi_types::free_error`.
///
///  When the instance is no longer needed, it should be released with
///  [`free_server_session`].
///
///  # Safety
///
///  config is a valid, properly aligned pointer to a SessionConfig object. Once
///  the config object has been provided here, it should not be used again.
#[no_mangle]
pub unsafe extern "C" fn new_server_session(
    session_config: *mut SessionConfig,
) -> ErrorOrServerSession {
    let session_config = Box::from_raw(session_config);
    let server_session = ServerSession::create(*session_config);

    match server_session {
        Ok(session) => ErrorOrServerSession {
            result: Box::into_raw(Box::new(session)),
            error: std::ptr::null(),
        },
        Err(e) => ErrorOrServerSession {
            result: std::ptr::null_mut(),
            error: Error::new_raw(e.to_string()),
        },
    }
}

///  Calls [`ServerSession::is_open`] on the provided `ServerSession`
///
///  # Safety
///
///  The provided [`ServerSession`] pointer should be non-null, properly
///  aligned, and points to a valid [`ServerSession`] instance.
#[no_mangle]
pub unsafe extern "C" fn server_is_open(session: *const ServerSession) -> bool {
    (*session).is_open()
}

///  Calls [`ServerSession:put_incoming_message`] on the provided
///  [`ServerSession`] pointer.
///
///  If the call results in an error, a non-null error containing a string
///  descripton of the Rust error will be returned.
///
///  If a non-null error is returned, it should be freed with free_error.
///
///  # Safety
///
///  * The provided [`ServerSession`] pointer should be non-null, properly
///    aligned, and points to a valid [`ServerSession`] instance.
///
///  * The provided [`BytesView`] is valid.
#[no_mangle]
pub unsafe extern "C" fn server_put_incoming_message(
    session: *mut ServerSession,
    request_bytes: BytesView,
) -> *const Error {
    safe_server_put_incoming_message(&mut *session, request_bytes.as_slice())
}

fn safe_server_put_incoming_message(
    session: &mut ServerSession,
    request_slice: &[u8],
) -> *const Error {
    let request = match SessionRequest::decode(request_slice) {
        Ok(r) => r,
        Err(e) => return Error::new_raw(e.to_string()),
    };

    let result = (*session).put_incoming_message(&request);

    match result {
        Ok(_) => std::ptr::null(),
        Err(e) => Error::new_raw(e.to_string()),
    }
}

///  Calls [`ServerSession::get_outgoing_message`] on the provided
///  [`ServerSession`] pointer.
///
///  If the call results in an error, the `error` field of the result will be
///  populated with a string decription of the Rust error.
///
///  If non-null bytes are returned, they should be freed with free_bytes.
///  If a non-null error is returned, it should be freed with free_error.
///
///  # Safety
///
///  The provided [`ServerSession`] pointer should be non-null, properly
///  aligned, and points to a valid [`ServerSession`] instance.
#[no_mangle]
pub unsafe extern "C" fn server_get_outgoing_message(
    session: *mut ServerSession,
) -> ErrorOrRustBytes {
    safe_server_get_outgoing_message(&mut *session)
}

fn safe_server_get_outgoing_message(session: &mut ServerSession) -> ErrorOrRustBytes {
    let outgoing_message = match session.get_outgoing_message() {
        Ok(Some(om)) => om,
        Ok(None) => return ErrorOrRustBytes::null(),
        Err(e) => return ErrorOrRustBytes::err(e.to_string()),
    };

    ErrorOrRustBytes::ok(Message::encode_to_vec(&outgoing_message).into_boxed_slice())
}

///  Calls [`ServerSession::read`] on the provided [`ServerSession`] pointer.
///
/// THe returned [`Bytes`] will contain the `plaintext` field of the
/// [`PlaintextMessage`] proto returned by the underlying library.
///
/// We make this divergence from the underlying Rust API to
/// avoid the copy/serialization/deserialization overhead associated with
/// passing the proto back and forth.
///
///  If the call results in an error, the `error` field of the result will be
///  populated with a string decription of the Rust error.
///
///  If non-null bytes are returned, they should be freed with free_bytes.
///  If a non-null error is returned, it should be freed with free_error.
///
///  # Safety
///
///  The provided [`ServerSession`] pointer should be non-null, properly
///  aligned, and points to a valid [`ServerSession`] instance.
#[no_mangle]
pub unsafe extern "C" fn server_read(session: *mut ServerSession) -> ErrorOrRustBytes {
    safe_server_read(&mut *session)
}

fn safe_server_read(session: &mut ServerSession) -> ErrorOrRustBytes {
    let decrypted_message = match session.read() {
        Ok(Some(om)) => om,
        Ok(None) => return ErrorOrRustBytes::null(),
        Err(e) => return ErrorOrRustBytes::err(e.to_string()),
    };

    ErrorOrRustBytes::ok(decrypted_message.plaintext.into_boxed_slice())
}

///  Calls [`ServerSession::write`] on the provided
///  [`ServerSession`] pointer.
///
/// The provided `Bytes` should be the raw application bytes to be encrypted.
/// They'll be added to a `PlaintextMessage` proto by the library
/// implementation. We make this divergence from the underlying Rust API to
/// avoid the copy/serialization/deserialization overhead associated with
/// passing the proto back and forth.
///
///  If the call results in an error, the `error` field of the result will be
///  populated with a string decription of the Rust error.
///
///  If non-null bytes are returned, they should be freed with free_bytes.
///  If a non-null error is returned, it should be freed with free_error.
///
///  # Safety
///
///  * The provided [`ServerSession`] pointer should be non-null, properly
///    aligned, and points to a valid [`ServerSession`] instance.
///
///  * The provided [`BytesView`] is valid.
#[no_mangle]
pub unsafe extern "C" fn server_write(
    session: *mut ServerSession,
    plaintext_message_bytes: BytesView,
) -> *const Error {
    safe_server_write(&mut *session, plaintext_message_bytes.as_slice())
}

fn safe_server_write(session: &mut ServerSession, plaintext_slice: &[u8]) -> *const Error {
    match session.write(&PlaintextMessage { plaintext: plaintext_slice.to_vec() }) {
        Ok(()) => std::ptr::null(),
        Err(e) => Error::new_raw(e.to_string()),
    }
}

///  Return ownership of the [`ServerSession`] pointer to Rust, where it will be
///  dropped and all related memory released.
///
///  Every call to `new_server_session` should be paired with this call.
///
///  # Safety
///
///  * The provided [`ServerSession`] pointer should be non-null, properly
///    aligned, and points to a valid [`ServerSession`] instance.
///  * The pointer should not be used anymore after calling this function.
#[no_mangle]
pub unsafe extern "C" fn free_server_session(session: *mut ServerSession) {
    drop(Box::from_raw(session));
}

#[repr(C)]
pub struct ErrorOrServerSession {
    pub result: *mut ServerSession,
    pub error: *const Error,
}
