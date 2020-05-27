// Copyright 2017-2019 int08h LLC
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

//!
//! Represents the server's long-term identity.
//!

use std::fmt;
use std::fmt::Formatter;

use crate::key::OnlineKey;
use crate::message::RtMessage;
use crate::sign::Signer;
use crate::tag::Tag;
use crate::CERTIFICATE_CONTEXT;

///
/// Represents the server's long-term identity.
///
pub struct LongTermKey {
    signer: Signer,
}

impl LongTermKey {
    pub fn new(seed: &[u8]) -> Self {
        LongTermKey {
            signer: Signer::from_seed(seed),
        }
    }

    /// Create a CERT message with a DELE containing the provided online key
    /// and a SIG of the DELE value signed by the long-term key
    pub fn make_cert(&mut self, online_key: &OnlineKey) -> RtMessage {
        let dele_bytes = online_key.make_dele().encode().unwrap();

        self.signer.update(CERTIFICATE_CONTEXT.as_bytes());
        self.signer.update(&dele_bytes);

        let dele_signature = self.signer.sign();

        let mut cert_msg = RtMessage::new(2);
        cert_msg.add_field(Tag::SIG, &dele_signature).unwrap();
        cert_msg.add_field(Tag::DELE, &dele_bytes).unwrap();

        cert_msg
    }

    /// Return the public key for the provided seed
    pub fn public_key(&self) -> &[u8] {
        self.signer.public_key_bytes()
    }
}

impl fmt::Display for LongTermKey {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.signer)
    }
}
