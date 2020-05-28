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
//!

use ring::rand;
use ring::rand::SecureRandom;
use ring::signature;
use ring::signature::Ed25519KeyPair;

use untrusted::Input;

use std::fmt;
use std::fmt::Formatter;

const INITIAL_BUF_SIZE: usize = 1024;

/// A multi-step (init-update-finish) interface for verifying an Ed25519 signature
#[derive(Debug)]
pub struct Verifier<'a> {
    pubkey: Input<'a>,
    buf: Vec<u8>,
}

impl<'a> Verifier<'a> {
    pub fn new(pubkey: &'a [u8]) -> Self {
        Verifier {
            pubkey: Input::from(pubkey),
            buf: Vec::with_capacity(INITIAL_BUF_SIZE),
        }
    }

    pub fn update(&mut self, data: &[u8]) {
        self.buf.reserve(data.len());
        self.buf.extend_from_slice(data);
    }

    pub fn verify(&self, expected_sig: &[u8]) -> bool {
        let msg = Input::from(&self.buf);
        let sig = Input::from(expected_sig);

        match signature::verify(&signature::ED25519, self.pubkey, msg, sig) {
            Ok(_) => true,
            _ => false,
        }
    }
}

/// A multi-step (init-update-finish) interface for creating an Ed25519 signature
pub struct Signer {
    key_pair: Ed25519KeyPair,
    buf: Vec<u8>,
}

impl Default for Signer {
    fn default() -> Self {
        Self::new()
    }
}

impl Signer {
    pub fn new() -> Self {
        let rng = rand::SystemRandom::new();
        let mut seed = [0u8; 32];
        rng.fill(&mut seed).unwrap();

        Signer::from_seed(&seed)
    }

    pub fn from_seed(seed: &[u8]) -> Self {
        let seed_input = Input::from(seed);
        Signer {
            key_pair: Ed25519KeyPair::from_seed_unchecked(seed_input).unwrap(),
            buf: Vec::with_capacity(INITIAL_BUF_SIZE),
        }
    }

    pub fn update(&mut self, data: &[u8]) {
        self.buf.reserve(data.len());
        self.buf.extend_from_slice(data);
    }

    pub fn sign(&mut self) -> Vec<u8> {
        let signature = self.key_pair.sign(&self.buf).as_ref().to_vec();
        self.buf.clear();

        signature
    }

    pub fn public_key_bytes(&self) -> &[u8] {
        self.key_pair.public_key_bytes()
    }
}

impl fmt::Display for Signer {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", hex::encode(self.public_key_bytes()))
    }
}

impl fmt::Debug for Signer {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(
            f,
            "Signer({}, {:?})",
            hex::encode(self.public_key_bytes()),
            self.buf
        )
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

    #[test]
    fn sign_ed25519_empty_message() {
        let seed = hex::decode("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")
            .unwrap();

        let expected_sig = hex::decode(
            "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"
        ).unwrap();

        let mut s = Signer::from_seed(&seed);
        let sig = s.sign();
        assert_eq!(sig, expected_sig);
    }

    #[test]
    fn sign_ed25519_message() {
        let seed = hex::decode("0d4a05b07352a5436e180356da0ae6efa0345ff7fb1572575772e8005ed978e9")
            .unwrap();

        let message = hex::decode("cbc77b").unwrap();

        let expected_sig = hex::decode(
            "d9868d52c2bebce5f3fa5a79891970f309cb6591e3e1702a70276fa97c24b3a8e58606c38c9758529da50ee31b8219cba45271c689afa60b0ea26c99db19b00c"
        ).unwrap();

        let mut s = Signer::from_seed(&seed);
        s.update(&message);
        let sig = s.sign();
        assert_eq!(sig, expected_sig);
    }

    #[test]
    fn sign_verify_round_trip() {
        let seed = hex::decode("334a05b07352a5436e180356da0ae6efa0345ff7fb1572575772e8005ed978e9")
            .unwrap();

        let message = "Hello world".as_bytes();

        let mut signer = Signer::from_seed(&seed);
        signer.update(&message);
        let signature = signer.sign();

        let mut v = Verifier::new(signer.public_key_bytes());
        v.update(&message);
        let result = v.verify(&signature);

        assert_eq!(result, true);
    }
}
