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
//! A multi-step (init-update-finish) interface for Ed25519 signing and verification

use ring::signature;

const INITIAL_BUF_SIZE: usize = 1024;

/// A multi-step (init-update-finish) interface for verifying an Ed25519 signature
#[derive(Debug)]
pub struct Verifier {
    pubkey: Vec<u8>,
    buf: Vec<u8>,
}

impl Verifier {
    pub fn new(pubkey: &[u8]) -> Self {
        Verifier {
            pubkey: pubkey.to_owned(),
            buf: Vec::with_capacity(INITIAL_BUF_SIZE),
        }
    }

    pub fn update(&mut self, data: &[u8]) {
        self.buf.reserve(data.len());
        self.buf.extend_from_slice(data);
    }

    pub fn verify(&self, expected_sig: &[u8]) -> bool {
        let public_key = signature::UnparsedPublicKey::new(&signature::ED25519, &self.pubkey);
        match public_key.verify(&self.buf, expected_sig) {
            Ok(_) => true,
            _ => false,
        }
    }
}

#[rustfmt::skip] // rustfmt errors on the long signature strings
#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn verify_ed25519_sig_on_empty_message() {
        let pubkey = hex::decode(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
        ).unwrap();

        let signature = hex::decode(
            "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"
        ).unwrap();

        let v = Verifier::new(&pubkey);
        let result = v.verify(&signature);
        assert_eq!(result, true);
    }

    #[test]
    fn verify_ed25519_sig() {
        let pubkey = hex::decode(
            "c0dac102c4533186e25dc43128472353eaabdb878b152aeb8e001f92d90233a7",
        ).unwrap();

        let message = hex::decode("5f4c8989").unwrap();

        let signature = hex::decode(
            "124f6fc6b0d100842769e71bd530664d888df8507df6c56dedfdb509aeb93416e26b918d38aa06305df3095697c18b2aa832eaa52edc0ae49fbae5a85e150c07"
        ).unwrap();

        let mut v = Verifier::new(&pubkey);
        v.update(&message);
        let result = v.verify(&signature);
        assert_eq!(result, true);
    }
}
