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
use oak_crypto::identity_key::IdentityKey;
use oak_ffi_bytes::{BytesView, free_rust_bytes, free_rust_bytes_contents};
use oak_proto_rust::oak::session::v1::{SessionRequest, SessionResponse};
use oak_session::{
    Session,
    session::{ClientSession, ServerSession},
};
use oak_session_ffi_attestation::{new_simple_attester, new_simple_endorser};
use oak_session_ffi_client_session as client_ffi;
use oak_session_ffi_config::{
    self as config_ffi, identity_key_get_public_key, new_identity_key,
    session_config_builder_add_peer_verifier, session_config_builder_add_self_attester,
    session_config_builder_add_self_endorser, session_config_builder_add_session_binder,
    session_config_builder_set_peer_static_public_key,
    session_config_builder_set_self_static_private_key,
};
use oak_session_ffi_server_session as server_ffi;
use oak_session_ffi_testing::{
    free_signing_key, new_fake_attestation_verifier, new_fake_endorsements, new_fake_evidence,
    new_random_signing_key, signing_key_verifying_key_bytes,
};
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
fn test_nn_handshake() {
    let client_session_ptr = create_client_session(create_unattested_nn_session_config());
    let server_session_ptr = create_server_session(create_unattested_nn_session_config());

    unsafe { do_handshake(client_session_ptr, server_session_ptr) };

    assert!(unsafe { client_ffi::client_is_open(client_session_ptr) });
    assert!(unsafe { server_ffi::server_is_open(server_session_ptr) });
    unsafe { client_ffi::free_client_session(client_session_ptr) };
    unsafe { server_ffi::free_server_session(server_session_ptr) };
}

#[test]
fn test_nk_handshake() {
    let identity_key = new_identity_key();
    let client_session_ptr =
        create_client_session(create_unattested_nk_client_session_config(identity_key));
    let server_session_ptr =
        create_server_session(create_unattested_nk_server_session_config(identity_key));

    unsafe { do_handshake(client_session_ptr, server_session_ptr) };

    assert!(unsafe { client_ffi::client_is_open(client_session_ptr) });
    assert!(unsafe { server_ffi::server_is_open(server_session_ptr) });
    unsafe { client_ffi::free_client_session(client_session_ptr) };
    unsafe { server_ffi::free_server_session(server_session_ptr) };
}

#[test]
fn test_kk_handshake() {
    let client_identity_key = new_identity_key();
    let client_pk_result = unsafe { identity_key_get_public_key(client_identity_key) };
    assert_no_error!(client_pk_result.error);

    let server_identity_key = new_identity_key();
    let server_pk_result = unsafe { identity_key_get_public_key(server_identity_key) };
    assert_no_error!(server_pk_result.error);

    let client_session_ptr = create_client_session(create_unattested_kk_session_config(
        (unsafe { *server_pk_result.result }).as_bytes_view(),
        client_identity_key,
    ));
    let server_session_ptr = create_server_session(create_unattested_kk_session_config(
        (unsafe { *client_pk_result.result }).as_bytes_view(),
        server_identity_key,
    ));

    unsafe { do_handshake(client_session_ptr, server_session_ptr) };

    assert!(unsafe { client_ffi::client_is_open(client_session_ptr) });
    assert!(unsafe { server_ffi::server_is_open(server_session_ptr) });
    unsafe { free_rust_bytes(client_pk_result.result) };
    unsafe { free_rust_bytes(server_pk_result.result) };
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
    unsafe { free_rust_bytes(decrypted_result.result) };
    unsafe { free_rust_bytes(encrypted_result.result) };
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
    unsafe { free_rust_bytes(encrypted_result.result) };
    unsafe { free_rust_bytes(decrypted_result.result) };
    unsafe { client_ffi::free_client_session(client_session_ptr) };
    unsafe { server_ffi::free_server_session(server_session_ptr) };
}

#[test]
fn test_client_encrypt_server_decrypt_with_attestation() {
    let client_session_ptr = create_client_session(create_attested_nn_client_session_config());
    let server_session_ptr = create_server_session(create_attested_nn_server_session_config());

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
    unsafe { free_rust_bytes(decrypted_result.result) };
    unsafe { free_rust_bytes(encrypted_result.result) };
    unsafe { client_ffi::free_client_session(client_session_ptr) };
    unsafe { server_ffi::free_server_session(server_session_ptr) };
}

#[test]
fn test_server_encrypt_client_decrypt_with_attestation() {
    let client_session_ptr = create_client_session(create_attested_nn_client_session_config());
    let server_session_ptr = create_server_session(create_attested_nn_server_session_config());
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
    unsafe { free_rust_bytes(encrypted_result.result) };
    unsafe { free_rust_bytes(decrypted_result.result) };
    unsafe { client_ffi::free_client_session(client_session_ptr) };
    unsafe { server_ffi::free_server_session(server_session_ptr) };
}

unsafe fn do_handshake(
    client_session_ptr: *mut ClientSession,
    server_session_ptr: *mut ServerSession,
) {
    while unsafe { !(*client_session_ptr).is_open() && !(*server_session_ptr).is_open() } {
        if unsafe { !(*client_session_ptr).is_open() } {
            let init = unsafe { client_ffi::client_get_outgoing_message(client_session_ptr) };
            assert_no_error!(init.error);
            let incoming_slice = unsafe { (*init.result).as_slice() };
            let _ = SessionRequest::decode(incoming_slice).expect("couldn't decode init request");
            let result = unsafe {
                server_ffi::server_put_incoming_message(
                    server_session_ptr,
                    (*init.result).as_bytes_view(),
                )
            };
            assert_no_error!(result);
            unsafe { free_rust_bytes(init.result) };
        }

        if unsafe { !(*server_session_ptr).is_open() } {
            let init_resp = unsafe { server_ffi::server_get_outgoing_message(server_session_ptr) };
            assert_no_error!(init_resp.error);
            if !init_resp.result.is_null() {
                let init_resp_slice = unsafe { (*init_resp.result).as_slice() };
                let _ = SessionResponse::decode(init_resp_slice)
                    .expect("couldn't decode init response");
                let put_result = unsafe {
                    client_ffi::client_put_incoming_message(
                        client_session_ptr,
                        (*init_resp.result).as_bytes_view(),
                    )
                };
                assert_no_error!(put_result);
                unsafe { free_rust_bytes(init_resp.result) };
            }
        }
    }
}

const FAKE_ATTESTER_ID: &[u8] = b"fake_attester";

fn create_unattested_nn_session_config() -> *mut oak_session::config::SessionConfig {
    let session_config_builder = config_ffi::new_session_config_builder(
        config_ffi::ATTESTATION_TYPE_UNATTESTED,
        config_ffi::HANDSHAKE_TYPE_NOISE_NN,
    );
    assert_no_error!(session_config_builder.error);
    unsafe { config_ffi::session_config_builder_build(session_config_builder.result) }
}

fn create_unattested_nk_client_session_config(
    identity_key: *const IdentityKey,
) -> *mut oak_session::config::SessionConfig {
    let session_config_builder_result = config_ffi::new_session_config_builder(
        config_ffi::ATTESTATION_TYPE_UNATTESTED,
        config_ffi::HANDSHAKE_TYPE_NOISE_NK,
    );
    assert_no_error!(session_config_builder_result.error);
    let mut session_config_builder = session_config_builder_result.result;

    let public_key_result = unsafe { identity_key_get_public_key(identity_key) };
    assert_no_error!(public_key_result.error);

    session_config_builder = unsafe {
        session_config_builder_set_peer_static_public_key(
            session_config_builder,
            (*public_key_result.result).as_bytes_view(),
        )
    };

    unsafe { free_rust_bytes(public_key_result.result) }
    unsafe { config_ffi::session_config_builder_build(session_config_builder) }
}

fn create_unattested_nk_server_session_config(
    identity_key: *mut IdentityKey,
) -> *mut oak_session::config::SessionConfig {
    let session_config_builder_result = config_ffi::new_session_config_builder(
        config_ffi::ATTESTATION_TYPE_UNATTESTED,
        config_ffi::HANDSHAKE_TYPE_NOISE_NK,
    );
    assert_no_error!(session_config_builder_result.error);
    let mut session_config_builder = session_config_builder_result.result;

    session_config_builder = unsafe {
        session_config_builder_set_self_static_private_key(session_config_builder, identity_key)
    };

    unsafe { config_ffi::session_config_builder_build(session_config_builder) }
}

fn create_unattested_kk_session_config(
    peer_public_key: BytesView,
    self_identity_key: *mut IdentityKey,
) -> *mut oak_session::config::SessionConfig {
    let session_config_builder_result = config_ffi::new_session_config_builder(
        config_ffi::ATTESTATION_TYPE_UNATTESTED,
        config_ffi::HANDSHAKE_TYPE_NOISE_KK,
    );
    assert_no_error!(session_config_builder_result.error);
    let mut session_config_builder = session_config_builder_result.result;

    session_config_builder = unsafe {
        session_config_builder_set_self_static_private_key(
            session_config_builder,
            self_identity_key,
        )
    };

    session_config_builder = unsafe {
        session_config_builder_set_peer_static_public_key(session_config_builder, peer_public_key)
    };

    unsafe { config_ffi::session_config_builder_build(session_config_builder) }
}

fn create_attested_nn_server_session_config() -> *mut oak_session::config::SessionConfig {
    let session_config_builder_result = config_ffi::new_session_config_builder(
        config_ffi::ATTESTATION_TYPE_SELF_UNIDIRECTIONAL,
        config_ffi::HANDSHAKE_TYPE_NOISE_NN,
    );
    assert_eq!(session_config_builder_result.error, std::ptr::null_mut());
    let mut session_config_builder = session_config_builder_result.result;

    let signing_key = new_random_signing_key();
    let verifying_key_bytes = unsafe { signing_key_verifying_key_bytes(signing_key) };
    let fake_evidence = unsafe {
        new_fake_evidence(
            verifying_key_bytes.as_bytes_view(),
            BytesView::new_from_slice(b"fake event"),
        )
    };
    unsafe { free_rust_bytes_contents(verifying_key_bytes) };

    let attester_result = unsafe { new_simple_attester(fake_evidence.as_bytes_view()) };
    assert_no_error!(attester_result.error);

    unsafe { free_rust_bytes_contents(fake_evidence) };

    session_config_builder = unsafe {
        session_config_builder_add_self_attester(
            session_config_builder,
            BytesView::new_from_slice(FAKE_ATTESTER_ID),
            attester_result.result,
        )
    };
    let fake_endorsements =
        unsafe { new_fake_endorsements(BytesView::new_from_slice(b"fake platform")) };
    let endorser_result = unsafe { new_simple_endorser(fake_endorsements.as_bytes_view()) };
    assert_no_error!(endorser_result.error);

    unsafe { free_rust_bytes_contents(fake_endorsements) };

    session_config_builder = unsafe {
        session_config_builder_add_self_endorser(
            session_config_builder,
            BytesView::new_from_slice(FAKE_ATTESTER_ID),
            endorser_result.result,
        )
    };

    session_config_builder = unsafe {
        session_config_builder_add_session_binder(
            session_config_builder,
            BytesView::new_from_slice(FAKE_ATTESTER_ID),
            signing_key,
        )
    };
    unsafe { free_signing_key(signing_key) };
    unsafe { config_ffi::session_config_builder_build(session_config_builder) }
}

fn create_attested_nn_client_session_config() -> *mut oak_session::config::SessionConfig {
    let session_config_builder_result = config_ffi::new_session_config_builder(
        config_ffi::ATTESTATION_TYPE_PEER_UNIDIRECTIONAL,
        config_ffi::HANDSHAKE_TYPE_NOISE_NN,
    );
    assert_eq!(session_config_builder_result.error, std::ptr::null_mut());
    let mut session_config_builder = session_config_builder_result.result;

    let fake_attestation_verifier = unsafe {
        new_fake_attestation_verifier(
            BytesView::new_from_slice(b"fake event"),
            BytesView::new_from_slice(b"fake platform"),
        )
    };

    session_config_builder = unsafe {
        session_config_builder_add_peer_verifier(
            session_config_builder,
            BytesView::new_from_slice(FAKE_ATTESTER_ID),
            fake_attestation_verifier,
        )
    };

    unsafe { config_ffi::session_config_builder_build(session_config_builder) }
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
