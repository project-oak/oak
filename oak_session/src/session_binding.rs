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

//! This module provides traits that allow to bind the data to the session.
use alloc::{boxed::Box, vec::Vec};

use anyhow::Error;
use derive_builder::Builder;
#[cfg(test)]
use mockall::automock;
use oak_crypto::{signer::Signer, verifier::Verifier};

// Trait that allows binding session to the arbitrary data
#[cfg_attr(test, automock)]
pub trait SessionBinder: Send {
    fn bind(&self, bound_data: &[u8]) -> Vec<u8>;
}

#[derive(Builder)]
#[builder(no_std)]
#[builder(pattern = "owned")]
pub struct SignatureBinder {
    signer: Box<dyn Signer>,
    #[builder(default)]
    additional_data: Vec<u8>,
}

impl SessionBinder for SignatureBinder {
    fn bind(&self, bound_data: &[u8]) -> Vec<u8> {
        self.signer.sign([bound_data, self.additional_data.as_slice()].concat().as_slice())
    }
}

// Trait that allows verifying the binding between the session and the arbitrary
// data.
#[cfg_attr(test, automock)]
pub trait SessionBindingVerifier: Send {
    fn verify_binding(&self, bound_data: &[u8], binding: &[u8]) -> Result<(), Error>;
}

#[derive(Builder)]
#[builder(no_std)]
#[builder(pattern = "owned")]
pub struct SignatureBindingVerifier {
    verifier: Box<dyn Verifier>,
    #[builder(default)]
    additional_data: Vec<u8>,
}

impl SessionBindingVerifier for SignatureBindingVerifier {
    fn verify_binding(&self, bound_data: &[u8], binding: &[u8]) -> Result<(), Error> {
        self.verifier
            .verify([bound_data, self.additional_data.as_slice()].concat().as_slice(), binding)
    }
}

#[cfg(test)]
mod tests {
    use p256::ecdsa::{SigningKey, VerifyingKey};
    use rand_core::OsRng;

    use super::*;

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
}
