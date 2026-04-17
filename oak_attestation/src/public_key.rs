//
// Copyright 2025 The Project Oak Authors
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

//! This modules provides an `Attester` and `Endorser` for a session binding
//! public key.
//!
//! The `PublicKeyAttester` creates `Evidence` containing the public key, and
//! the `PublicKeyEndorser` creates `Endorsements` containing an endorsement for
//! that public key.

use alloc::{string::ToString, vec};

use anyhow::Result;
use oak_attestation_types::{attester::Attester, endorser::Endorser};
use oak_proto_rust::oak::{
    Variant,
    attestation::v1::{Endorsements, Event, EventLog, Evidence, SessionBindingPublicKeyData},
};
use p256::ecdsa::VerifyingKey;
use prost::Message;

/// An [`Attester`] that uses and ECDSA public key as the attestation
/// evidence. The public key needs to be endorsed, for exampels using
//  the [`PublicKeyEndorser`].
pub struct PublicKeyAttester {
    public_key: VerifyingKey,
}

impl PublicKeyAttester {
    /// Creates a new `PublicKeyAttester` for the provided public key.
    pub fn new(public_key: VerifyingKey) -> Self {
        Self { public_key }
    }
}

impl Attester for PublicKeyAttester {
    /// This is a leaf attester and does not support extending the evidence. It
    /// will always return an error.
    fn extend(&mut self, _encoded_event: &[u8]) -> Result<()> {
        anyhow::bail!("This is a leaf attester, it cannot extend the evidence")
    }

    /// Generates [`Evidence`] containing the session binding public key.
    ///
    /// The evidence contains a single event with the tag "session_binding_key"
    /// and the public key encoded as [`SessionBindingPublicKeyData`].
    fn quote(&self) -> Result<Evidence> {
        let event = Event {
            tag: "session_binding_key".to_string(),
            event: Some(prost_types::Any {
                type_url: "type.googleapis.com/oak.attestation.v1.SessionBindingPublicKeyData"
                    .to_string(),
                value: SessionBindingPublicKeyData {
                    session_binding_public_key: self.public_key.to_sec1_bytes().to_vec(),
                }
                .encode_to_vec(),
            }),
        };
        let evidence = Evidence {
            event_log: Some(EventLog { encoded_events: vec![event.encode_to_vec()] }),
            ..Default::default()
        };
        Ok(evidence)
    }
}

/// An [`Endorser`] that provides an endorsement for a session binding public
/// key. The endorsement is added as an Event into the endorsement event log,
/// using the [`SessionBindingPublicKeyEndorsement`] proto message.
pub struct PublicKeyEndorser<E> {
    endorsement: E,
}

impl<E> PublicKeyEndorser<E> {
    /// Creates a new `PublicKeyEndorser` with the provided pre-computed
    /// endorsement.
    pub fn new(endorsement: E) -> Self {
        Self { endorsement }
    }
}

impl<E: Message + Clone> Endorser for PublicKeyEndorser<E>
where
    Variant: From<E>,
{
    /// Wraps the provided [`SessionBindingPublicKeyEndorsement`] into the event
    /// log of the [`Endorsements`] endorsement type.
    ///
    /// This implementation ignores the provided [`Evidence`] as the endorsement
    /// is pre-computed.
    fn endorse(&self, _: Option<&Evidence>) -> Result<Endorsements> {
        let endorsements =
            Endorsements { events: vec![self.endorsement.clone().into()], ..Default::default() };
        Ok(endorsements)
    }
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;

    use googletest::prelude::*;
    use p256::ecdsa::SigningKey;

    use super::*;

    const SIGNING_KEY: &str = "
-----BEGIN PRIVATE KEY-----
MIGHAgEAMBMGByqGSM49AgEGCCqGSM49AwEHBG0wawIBAQQgrvnMHLTorFFIv81o
tY7X8XNBXwBH9yNp9Nza8ymFRbmhRANCAAShmAYmC7YQ2SHOzTaugBQDSVQrjwnh
Nj98VHCkMOChdP0NoY0+ASi3S9WesDHql/SS3TeVKIW0W7VRIYDz51rU
-----END PRIVATE KEY-----
";

    #[googletest::test]
    fn test_public_key_attester_extend() -> googletest::Result<()> {
        let signing_key = SigningKey::from_str(SIGNING_KEY).expect("parsing key");
        let public_key = signing_key.verifying_key();
        let mut attester = PublicKeyAttester::new(*public_key);
        let result = attester.extend(&[]);

        assert_that!(result, err(anything()));

        Ok(())
    }

    #[googletest::test]
    fn test_public_key_attester_quote() -> googletest::Result<()> {
        let signing_key = SigningKey::from_str(SIGNING_KEY).expect("parsing key");
        let verifying_key = *signing_key.verifying_key();
        let attester = PublicKeyAttester::new(verifying_key);

        let evidence = attester.quote().expect("quote failed");

        assert_that!(evidence.event_log, some(anything()));
        assert_that!(evidence.event_log.unwrap().encoded_events, len(eq(1)));

        Ok(())
    }
}
