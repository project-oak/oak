//
// Copyright 2020 The Project Oak Authors
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

use anyhow::Context;
use pem::Pem;
use ring::{
    rand,
    signature::{self, Ed25519KeyPair, KeyPair},
};
use std::{
    collections::HashMap,
    fs::{read, write},
};

// PEM file tags.
pub const PRIVATE_KEY_TAG: &str = "PRIVATE KEY";
pub const PUBLIC_KEY_TAG: &str = "PUBLIC KEY";
pub const SIGNATURE_TAG: &str = "SIGNATURE";
pub const HASH_TAG: &str = "HASH";

/// Convenience struct that encapsulates `Ed25519KeyPair`.
/// Named `KeyBundle` since it uses the `ring::signature::KeyPair` trait.
pub struct KeyBundle {
    private_key: Vec<u8>,
    key_pair: Ed25519KeyPair,
}

impl KeyBundle {
    /// Generates a Ed25519 key pair.
    pub fn generate() -> anyhow::Result<KeyBundle> {
        let rng = rand::SystemRandom::new();
        let private_key = Ed25519KeyPair::generate_pkcs8(&rng)
            .ok()
            .context("Couldn't generate key pair")?;
        KeyBundle::parse(private_key.as_ref())
    }

    /// Parses a Ed25519 key pair from bytes.
    pub fn parse(private_key: &[u8]) -> anyhow::Result<KeyBundle> {
        let key_pair = Ed25519KeyPair::from_pkcs8(private_key)
            .ok()
            .context("Couldn't parse generated key pair")?;
        Ok(Self {
            private_key: private_key.to_vec(),
            key_pair,
        })
    }

    pub fn private_key(&self) -> Vec<u8> {
        self.private_key.to_vec()
    }

    pub fn public_key(&self) -> Vec<u8> {
        self.key_pair.public_key().as_ref().to_vec()
    }

    pub fn sign(&self, input: &[u8]) -> Vec<u8> {
        self.key_pair.sign(input).as_ref().to_vec()
    }
}

#[derive(Default, Clone)]
pub struct SignatureBundle {
    pub public_key: Vec<u8>,
    pub signed_hash: Vec<u8>,
    pub hash: Vec<u8>,
}

impl SignatureBundle {
    /// Signs a SHA-256 hash of the `input` using `private_key`.
    pub fn create(input: &[u8], key_pair: &KeyBundle) -> anyhow::Result<SignatureBundle> {
        let hash = get_sha256(input);
        Ok(SignatureBundle {
            public_key: key_pair.public_key(),
            signed_hash: key_pair.sign(&hash),
            hash,
        })
    }

    /// Verifies the signature validity.
    pub fn verify(&self) -> anyhow::Result<()> {
        let public_key = signature::UnparsedPublicKey::new(&signature::ED25519, &self.public_key);
        public_key
            .verify(&self.hash, &self.signed_hash)
            .ok()
            .with_context(|| {
                format!(
                    "Input file signature verification failed for {}",
                    hex::encode(&self.hash)
                )
            })?;
        Ok(())
    }

    /// Parses public key, signature and SHA-256 hash encoded using PEM format.
    /// https://tools.ietf.org/html/rfc1421
    pub fn from_pem_file(filename: &str) -> anyhow::Result<SignatureBundle> {
        let file =
            read(filename).with_context(|| format!("Couldn't read signature file {}", filename))?;
        let file_content: HashMap<String, Vec<u8>> = pem::parse_many(file)
            .iter()
            .map(|entry| (entry.tag.to_string(), entry.contents.to_vec()))
            .collect();
        let public_key = file_content
            .get(PUBLIC_KEY_TAG)
            .context("Signature file doesn't contain public key")?;
        let signed_hash = file_content
            .get(SIGNATURE_TAG)
            .context("Signature file doesn't contain signature")?;
        let hash = file_content
            .get(HASH_TAG)
            .context("Signature file doesn't contain hash")?;
        Ok(SignatureBundle {
            public_key: public_key.to_vec(),
            signed_hash: signed_hash.to_vec(),
            hash: hash.to_vec(),
        })
    }

    pub fn to_pem_file(&self, filename: &str) -> anyhow::Result<()> {
        let public_key_pem = create_pem(PUBLIC_KEY_TAG, &self.public_key);
        let signature_pem = create_pem(SIGNATURE_TAG, &self.signed_hash);
        let hash_pem = create_pem(HASH_TAG, &self.hash);
        let encoded_signature = pem::encode_many(&[public_key_pem, signature_pem, hash_pem]);
        write(filename, &encoded_signature)
            .with_context(|| format!("Couldn't write signature file {}", filename))?;
        Ok(())
    }
}

/// Creates a PEM structure for encoding.
fn create_pem(tag: &str, contents: &[u8]) -> Pem {
    Pem {
        tag: tag.to_string(),
        contents: contents.to_vec(),
    }
}

pub fn read_pem_file(filename: &str) -> anyhow::Result<Vec<u8>> {
    let file = read(filename).with_context(|| format!("Couldn't read PEM file {}", filename))?;
    let file_content = pem::parse(file)
        .context("Couldn't parse PEM encoded file")?
        .contents;
    Ok(file_content)
}

pub fn write_pem_file(filename: &str, tag: &str, contents: &[u8]) -> anyhow::Result<()> {
    let encoded_pem = pem::encode(&Pem {
        tag: tag.to_string(),
        contents: contents.to_vec(),
    });
    write(filename, encoded_pem).with_context(|| format!("Couldn't write file {}", filename))?;
    Ok(())
}

/// Computes a SHA-256 digest of `input` and returns it in a form of raw bytes.
pub fn get_sha256(input: &[u8]) -> Vec<u8> {
    use sha2::digest::Digest;
    let mut hasher = sha2::Sha256::new();
    hasher.update(&input);
    hasher.finalize().to_vec()
}

/// Computes a SHA-256 digest of `bytes` and returns it in a hex encoded string.
pub fn get_sha256_hex(bytes: &[u8]) -> String {
    let hash_value = get_sha256(bytes);
    hex::encode(hash_value)
}
