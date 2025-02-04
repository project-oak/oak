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
use oak_proto_rust::oak::session::v1::{SessionRequest, SessionResponse};
use oak_session::session::{ClientSession, ServerSession};
use oak_session_ffi_client_session as client_ffi;
use oak_session_ffi_config as config_ffi;
use oak_session_ffi_server_session as server_ffi;
use oak_session_ffi_types::BytesView;
use prost::Message;

#[test]
fn test_handshake() {
    let (client_session_ptr, server_session_ptr) = create_test_sessions();

    unsafe { do_handshake(client_session_ptr, server_session_ptr) };

    assert!(unsafe { client_ffi::client_is_open(client_session_ptr) });
    assert!(unsafe { server_ffi::server_is_open(server_session_ptr) });

    unsafe { free_test_sessions(client_session_ptr, server_session_ptr) };
}

#[test]
fn test_client_encrypt_server_decrypt() {
    let (client_session_ptr, server_session_ptr) = create_test_sessions();

    unsafe { do_handshake(client_session_ptr, server_session_ptr) };

    // Encrypt
    let message = b"Hello FFI World Client To Server";
    let plaintext_message_bytes = message.to_vec();
    let message_bytes = BytesView::new_from_slice(plaintext_message_bytes.as_slice());
    let write_result = unsafe { client_ffi::client_write(client_session_ptr, message_bytes) };
    assert_eq!(write_result, std::ptr::null_mut());
    let encrypted_result = unsafe { client_ffi::client_get_outgoing_message(client_session_ptr) };
    let encrypted_result_slice = unsafe { (*encrypted_result.result).as_slice() };
    let _ = SessionRequest::decode(encrypted_result_slice).expect("couldn't decode init request");
    assert_eq!(encrypted_result.error, std::ptr::null_mut());

    // Decrypt
    let put_result = unsafe {
        server_ffi::server_put_incoming_message(
            server_session_ptr,
            (*encrypted_result.result).as_bytes_view(),
        )
    };
    assert_eq!(put_result, std::ptr::null_mut());
    let decrypted_result = unsafe { server_ffi::server_read(server_session_ptr) };
    assert_eq!(decrypted_result.error, std::ptr::null_mut());

    assert_eq!(unsafe { (*decrypted_result.result).as_slice() }, message);
    unsafe { oak_session_ffi_types::free_rust_bytes(decrypted_result.result) };
    unsafe { oak_session_ffi_types::free_rust_bytes(encrypted_result.result) };
    unsafe { free_test_sessions(client_session_ptr, server_session_ptr) };
}

#[test]
fn test_server_encrypt_client_decrypt() {
    let (client_session_ptr, server_session_ptr) = create_test_sessions();
    unsafe { do_handshake(client_session_ptr, server_session_ptr) };

    // Encrypt
    let message = b"Hello FFI World Server To Client";
    let plaintext_message_bytes = message.to_vec();
    let message_bytes = BytesView::new_from_slice(plaintext_message_bytes.as_slice());
    let write_result = unsafe { server_ffi::server_write(server_session_ptr, message_bytes) };
    assert_eq!(write_result, std::ptr::null_mut());
    let encrypted_result = unsafe { server_ffi::server_get_outgoing_message(server_session_ptr) };
    let encrypted_result_slice = unsafe { (*encrypted_result.result).as_slice() };
    let _ = SessionRequest::decode(encrypted_result_slice).expect("couldn't decode init request");
    assert_eq!(encrypted_result.error, std::ptr::null_mut());

    // Decrypt
    let put_result = unsafe {
        client_ffi::client_put_incoming_message(
            client_session_ptr,
            (*encrypted_result.result).as_bytes_view(),
        )
    };
    assert_eq!(put_result, std::ptr::null_mut());
    let decrypted_result = unsafe { client_ffi::client_read(client_session_ptr) };
    assert_eq!(decrypted_result.error, std::ptr::null_mut());

    assert_eq!(unsafe { (*decrypted_result.result).as_slice() }, message);
    unsafe { oak_session_ffi_types::free_rust_bytes(encrypted_result.result) };
    unsafe { oak_session_ffi_types::free_rust_bytes(decrypted_result.result) };
    unsafe { free_test_sessions(client_session_ptr, server_session_ptr) };
}

unsafe fn do_handshake(
    client_session_ptr: *mut ClientSession,
    server_session_ptr: *mut ServerSession,
) {
    // Handshake
    let init = client_ffi::client_get_outgoing_message(client_session_ptr);
    assert_eq!(init.error, std::ptr::null_mut());
    let incoming_slice = (*init.result).as_slice();
    let _ = SessionRequest::decode(incoming_slice).expect("couldn't decode init request");

    let result =
        server_ffi::server_put_incoming_message(server_session_ptr, (*init.result).as_bytes_view());
    assert_eq!(result, std::ptr::null_mut());
    unsafe { oak_session_ffi_types::free_rust_bytes(init.result) };

    let init_resp = server_ffi::server_get_outgoing_message(server_session_ptr);
    assert_eq!(init_resp.error, std::ptr::null_mut());
    let init_resp_slice = (*init_resp.result).as_slice();
    let _ = SessionResponse::decode(init_resp_slice).expect("couldn't decode init response");
    let put_result = client_ffi::client_put_incoming_message(
        client_session_ptr,
        (*init_resp.result).as_bytes_view(),
    );
    unsafe { oak_session_ffi_types::free_rust_bytes(init_resp.result) };
    assert_eq!(put_result, std::ptr::null_mut());
}

fn create_test_session_config() -> *mut oak_session::config::SessionConfig {
    let session_config_builder = config_ffi::new_session_config_builder(
        config_ffi::ATTESTATION_TYPE_UNATTESTED,
        config_ffi::HANDSHAKE_TYPE_NOISE_NN,
    );
    assert_eq!(session_config_builder.error, std::ptr::null_mut());
    unsafe { config_ffi::session_config_builder_build(session_config_builder.result) }
}
fn create_test_sessions() -> (*mut ClientSession, *mut ServerSession) {
    let client_session_ptr_result =
        unsafe { client_ffi::new_client_session(create_test_session_config()) };
    assert_eq!(client_session_ptr_result.error, std::ptr::null_mut());
    let client_session_ptr = client_session_ptr_result.result;
    let server_session_ptr_result =
        unsafe { server_ffi::new_server_session(create_test_session_config()) };
    assert_eq!(server_session_ptr_result.error, std::ptr::null_mut());
    let server_session_ptr = server_session_ptr_result.result;
    (client_session_ptr, server_session_ptr)
}

unsafe fn free_test_sessions(
    client_session: *mut ClientSession,
    server_session: *mut ServerSession,
) {
    client_ffi::free_client_session(client_session);
    server_ffi::free_server_session(server_session);
}
