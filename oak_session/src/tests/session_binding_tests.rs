// Copyright 2025 Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use oak_session::session_binding::{
    SessionBinder, SessionBindingVerifier, SignatureBinderBuilder, SignatureBindingVerifierBuilder,
};
use p256::ecdsa::{SigningKey, VerifyingKey};
use rand_core::OsRng;

#[test]
fn verify_binding_succeeds() {
    let signing_key = SigningKey::random(&mut OsRng);
    let verifying_key = VerifyingKey::from(&signing_key);
    let bound_data = "bound data".as_bytes();

    let session_binder = SignatureBinderBuilder::default()
        .signer(Box::new(signing_key))
        .build()
        .expect("Failed to create the session binder");
    let session_binding_verifier = SignatureBindingVerifierBuilder::default()
        .verifier(Box::new(verifying_key))
        .build()
        .expect("Failed to create the session binding verifier");

    let binding = session_binder.bind(bound_data);
    session_binding_verifier.verify_binding(bound_data, binding.as_slice()).unwrap();
}

#[test]
fn verify_binding_succeeds_with_additional_data() {
    let signing_key = SigningKey::random(&mut OsRng);
    let verifying_key = VerifyingKey::from(&signing_key);
    let additional_data = "additional data".as_bytes();
    let bound_data = "bound data".as_bytes();

    let session_binder = SignatureBinderBuilder::default()
        .signer(Box::new(signing_key))
        .additional_data(additional_data.to_vec())
        .build()
        .expect("Failed to create the session binder");
    let session_binding_verifier = SignatureBindingVerifierBuilder::default()
        .verifier(Box::new(verifying_key))
        .additional_data(additional_data.to_vec())
        .build()
        .expect("Failed to create the session binding verifier");

    let binding = session_binder.bind(bound_data);
    session_binding_verifier.verify_binding(bound_data, binding.as_slice()).unwrap();
}

#[test]
fn verify_binding_fails_bound_data_mismatch() {
    let signing_key = SigningKey::random(&mut OsRng);
    let verifying_key = VerifyingKey::from(&signing_key);
    let additional_data = "additional data".as_bytes();
    let bound_data1 = "bound data 1".as_bytes();
    let bound_data2 = "bound data 2".as_bytes();

    let session_binder = SignatureBinderBuilder::default()
        .signer(Box::new(signing_key))
        .additional_data(additional_data.to_vec())
        .build()
        .expect("Failed to create the session binder");
    let session_binding_verifier = SignatureBindingVerifierBuilder::default()
        .verifier(Box::new(verifying_key))
        .additional_data(additional_data.to_vec())
        .build()
        .expect("Failed to create the session binding verifier");

    let binding = session_binder.bind(bound_data1);
    assert!(session_binding_verifier.verify_binding(bound_data2, binding.as_slice()).is_err());
}

#[test]
fn verify_binding_fails_additional_data_mismatch() {
    let signing_key = SigningKey::random(&mut OsRng);
    let verifying_key = VerifyingKey::from(&signing_key);
    let additional_data1 = "additional data 1".as_bytes();
    let additional_data2 = "additional data 2".as_bytes();
    let bound_data = "bound data".as_bytes();

    let session_binder = SignatureBinderBuilder::default()
        .signer(Box::new(signing_key))
        .additional_data(additional_data1.to_vec())
        .build()
        .expect("Failed to create the session binder");
    let session_binding_verifier = SignatureBindingVerifierBuilder::default()
        .verifier(Box::new(verifying_key))
        .additional_data(additional_data2.to_vec())
        .build()
        .expect("Failed to create the session binding verifier");

    let binding = session_binder.bind(bound_data);
    assert!(session_binding_verifier.verify_binding(bound_data, binding.as_slice()).is_err());
}
