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
use oak_proto_rust::oak::session::v1::{SessionRequest, SessionResponse};
use oak_session::{
    session::{ClientSession, ServerSession},
    Session,
};
use oak_session_ffi_client_session as client_ffi;
use oak_session_ffi_config as config_ffi;
use oak_session_ffi_server_session as server_ffi;
use oak_session_ffi_types::BytesView;
use prost::Message;

macro_rules! assert_no_error {
    ($error_ptr:expr) => {
        assert_eq!(
            $error_ptr,
            std::ptr::null(),
            "ERR: {}",
            String::from_utf8_lossy(unsafe { (*$error_ptr).message().as_slice() })
        );
    };
}

#[test]
fn test_handshake() {
    let client_session_ptr = create_client_session(create_unattested_nn_session_config());
    let server_session_ptr = create_server_session(create_unattested_nn_session_config());

    unsafe { do_handshake(client_session_ptr, server_session_ptr) };

    assert!(unsafe { client_ffi::client_is_open(client_session_ptr) });
    assert!(unsafe { server_ffi::server_is_open(server_session_ptr) });
    unsafe { client_ffi::free_client_session(client_session_ptr) };
    unsafe { server_ffi::free_server_session(server_session_ptr) };
}

#[test]
fn test_client_encrypt_server_decrypt() {
    let client_session_ptr = create_client_session(create_unattested_nn_session_config());
    let server_session_ptr = create_server_session(create_unattested_nn_session_config());

    unsafe { do_handshake(client_session_ptr, server_session_ptr) };

    // Encrypt
    let message = b"Hello FFI World Client To Server";
    let plaintext_message_bytes = message.to_vec();
    let message_bytes = BytesView::new_from_slice(plaintext_message_bytes.as_slice());
    let write_result = unsafe { client_ffi::client_write(client_session_ptr, message_bytes) };
    assert_no_error!(write_result);
    let encrypted_result = unsafe { client_ffi::client_get_outgoing_message(client_session_ptr) };
    let encrypted_result_slice = unsafe { (*encrypted_result.result).as_slice() };
    let _ = SessionRequest::decode(encrypted_result_slice).expect("couldn't decode init request");
    assert_no_error!(encrypted_result.error);

    // Decrypt
    let put_result = unsafe {
        server_ffi::server_put_incoming_message(
            server_session_ptr,
            (*encrypted_result.result).as_bytes_view(),
        )
    };
    assert_no_error!(put_result);
    let decrypted_result = unsafe { server_ffi::server_read(server_session_ptr) };
    assert_no_error!(decrypted_result.error);

    assert_eq!(unsafe { (*decrypted_result.result).as_slice() }, message);
    unsafe { oak_session_ffi_types::free_rust_bytes(decrypted_result.result) };
    unsafe { oak_session_ffi_types::free_rust_bytes(encrypted_result.result) };
    unsafe { client_ffi::free_client_session(client_session_ptr) };
    unsafe { server_ffi::free_server_session(server_session_ptr) };
}

#[test]
fn test_server_encrypt_client_decrypt() {
    let client_session_ptr = create_client_session(create_unattested_nn_session_config());
    let server_session_ptr = create_server_session(create_unattested_nn_session_config());
    unsafe { do_handshake(client_session_ptr, server_session_ptr) };

    // Encrypt
    let message = b"Hello FFI World Server To Client";
    let plaintext_message_bytes = message.to_vec();
    let message_bytes = BytesView::new_from_slice(plaintext_message_bytes.as_slice());
    let write_result = unsafe { server_ffi::server_write(server_session_ptr, message_bytes) };
    assert_no_error!(write_result);
    let encrypted_result = unsafe { server_ffi::server_get_outgoing_message(server_session_ptr) };
    let encrypted_result_slice = unsafe { (*encrypted_result.result).as_slice() };
    let _ = SessionRequest::decode(encrypted_result_slice).expect("couldn't decode init request");
    assert_no_error!(encrypted_result.error);

    // Decrypt
    let put_result = unsafe {
        client_ffi::client_put_incoming_message(
            client_session_ptr,
            (*encrypted_result.result).as_bytes_view(),
        )
    };
    assert_no_error!(put_result);
    let decrypted_result = unsafe { client_ffi::client_read(client_session_ptr) };
    assert_no_error!(decrypted_result.error);

    assert_eq!(unsafe { (*decrypted_result.result).as_slice() }, message);
    unsafe { oak_session_ffi_types::free_rust_bytes(encrypted_result.result) };
    unsafe { oak_session_ffi_types::free_rust_bytes(decrypted_result.result) };
    unsafe { client_ffi::free_client_session(client_session_ptr) };
    unsafe { server_ffi::free_server_session(server_session_ptr) };
}

unsafe fn do_handshake(
    client_session_ptr: *mut ClientSession,
    server_session_ptr: *mut ServerSession,
) {
    while !(*client_session_ptr).is_open() && !(*server_session_ptr).is_open() {
        if !(*client_session_ptr).is_open() {
            let init = client_ffi::client_get_outgoing_message(client_session_ptr);
            assert_no_error!(init.error);
            let incoming_slice = (*init.result).as_slice();
            let _ = SessionRequest::decode(incoming_slice).expect("couldn't decode init request");
            let result = server_ffi::server_put_incoming_message(
                server_session_ptr,
                (*init.result).as_bytes_view(),
            );
            assert_no_error!(result);
            unsafe { oak_session_ffi_types::free_rust_bytes(init.result) };
        }

        if !(*server_session_ptr).is_open() {
            let init_resp = server_ffi::server_get_outgoing_message(server_session_ptr);
            assert_no_error!(init_resp.error);
            if !init_resp.result.is_null() {
                let init_resp_slice = (*init_resp.result).as_slice();
                let _ = SessionResponse::decode(init_resp_slice)
                    .expect("couldn't decode init response");
                let put_result = client_ffi::client_put_incoming_message(
                    client_session_ptr,
                    (*init_resp.result).as_bytes_view(),
                );
                assert_no_error!(put_result);
                unsafe { oak_session_ffi_types::free_rust_bytes(init_resp.result) };
            }
        }
    }
}

fn create_unattested_nn_session_config() -> *mut oak_session::config::SessionConfig {
    let session_config_builder = config_ffi::new_session_config_builder(
        config_ffi::ATTESTATION_TYPE_UNATTESTED,
        config_ffi::HANDSHAKE_TYPE_NOISE_NN,
    );
    assert_no_error!(session_config_builder.error);
    unsafe { config_ffi::session_config_builder_build(session_config_builder.result) }
}

fn create_client_session(config: *mut oak_session::config::SessionConfig) -> *mut ClientSession {
    let client_session_ptr_result = unsafe { client_ffi::new_client_session(config) };
    assert_no_error!(client_session_ptr_result.error);
    client_session_ptr_result.result
}

fn create_server_session(config: *mut oak_session::config::SessionConfig) -> *mut ServerSession {
    let server_session_ptr_result = unsafe { server_ffi::new_server_session(config) };
    assert_no_error!(server_session_ptr_result.error);
    server_session_ptr_result.result
}
