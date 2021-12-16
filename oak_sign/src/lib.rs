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
use oak_abi::proto::oak::application::ModuleSignature;
use once_cell::sync::Lazy;
use pem::Pem;
use ring::{
    rand,
    signature::{self, Ed25519KeyPair},
};
#[allow(unused_imports)]
use simple_asn1::{ASN1Block, BigUint, OID};
use std::{
    collections::HashMap,
    fs::{read, write},
};

// PEM file tags.
pub const PRIVATE_KEY_TAG: &str = "PRIVATE KEY";
pub const PUBLIC_KEY_TAG: &str = "PUBLIC KEY";
pub const SIGNATURE_TAG: &str = "SIGNATURE";
pub const HASH_TAG: &str = "HASH";

/// Convenience struct that encapsulates `ring::signature::Ed25519KeyPair`.
#[derive(Debug)]
pub struct KeyPair {
    /// PKCS#8 v2 encoded private key and public key pair.
    /// https://tools.ietf.org/html/rfc5958
    ///
    /// The encoded version is kept because a parsed `key_pair` doesn't contain a method for
    /// extracting private key bytes.
    /// https://briansmith.org/rustdoc/ring/signature/struct.Ed25519KeyPair.html
    pkcs8: Vec<u8>,
    /// Parsed PKCS#8 v2 key pair representation.
    key_pair: Ed25519KeyPair,
}

impl Clone for KeyPair {
    fn clone(&self) -> Self {
        // The `clone` function is implemented as re-parsing, because `Ed25519KeyPair` doesn't
        // implement `Clone` and all of its fields are private.
        KeyPair::parse(&self.pkcs8).expect("Couldn't clone key pair")
    }
}

impl PartialEq for KeyPair {
    fn eq(&self, other: &Self) -> bool {
        // Currently only comparing that the encoded version is the same, since `Ed25519KeyPair`
        // doesn't implement `Eq` and all of its fields are private.
        // https://github.com/briansmith/ring/blob/8d4e283c16f335166b0e969ccc321acf0de39c0b/src/ec/curve25519/ed25519/signing.rs#L27-L37
        self.pkcs8 == other.pkcs8
    }
}

impl Eq for KeyPair {}

/// OID for the Ed25519 signature algorithm.
///
/// See:
///
/// - https://tools.ietf.org/html/rfc8419#section-2.2
/// - https://tools.ietf.org/html/rfc8410#section-3
/// - https://golang.org/src/crypto/x509/x509.go?s=3654:3712#L315
static OID_ED_25519: Lazy<OID> = Lazy::new(|| simple_asn1::oid!(1, 3, 101, 112));
static ED_25519_ALG: Lazy<ASN1Block> = Lazy::new(|| {
    ASN1Block::Sequence(
        0,
        vec![ASN1Block::ObjectIdentifier(0, OID_ED_25519.clone())],
    )
});

const BITS_PER_BYTE: usize = 8;

impl KeyPair {
    /// Generates a Ed25519 key pair.
    pub fn generate() -> anyhow::Result<KeyPair> {
        let rng = rand::SystemRandom::new();
        let key_pair_pkcs_8 = Ed25519KeyPair::generate_pkcs8(&rng)
            .ok()
            .context("Couldn't generate PKCS#8 key pair")?;
        KeyPair::parse(key_pair_pkcs_8.as_ref())
    }

    /// Parses a Ed25519 key pair from a PKCS#8 v2 encoded `pkcs8_key_pair`.
    pub fn parse(key_pair_pkcs_8: &[u8]) -> anyhow::Result<KeyPair> {
        let key_pair = Ed25519KeyPair::from_pkcs8(key_pair_pkcs_8)
            .ok()
            .context("Couldn't parse generated key pair")?;
        Ok(Self {
            pkcs8: key_pair_pkcs_8.to_vec(),
            key_pair,
        })
    }

    /// Returns a PKCS#8 v2 encoded key pair.
    pub fn key_pair_pkcs_8(&self) -> Vec<u8> {
        self.pkcs8.to_vec()
    }

    /// Returns the public key as a binary DER-encoded `SubjectPublicKeyInfo` (see
    /// https://tools.ietf.org/html/rfc5280#section-4.1).
    pub fn public_key_der(&self) -> anyhow::Result<Vec<u8>> {
        // Trait `ring::signature::KeyPair` that contains `public_key` function is included locally
        // in this function because it conflicts with [`KeyPair`].
        use ring::signature::KeyPair;
        let key_bytes = self.key_pair.public_key().as_ref().to_vec();
        encode_public_key_der(&key_bytes)
    }

    pub fn sign(&self, input: &[u8]) -> Vec<u8> {
        self.key_pair.sign(input).as_ref().to_vec()
    }
}

/// Encodes the public key as a binary DER-encoded `SubjectPublicKeyInfo` (see
/// https://tools.ietf.org/html/rfc5280#section-4.1).
pub fn encode_public_key_der(key_bytes: &[u8]) -> anyhow::Result<Vec<u8>> {
    // Offsets are only used when parsing ASN1, so we can just leave them as zeroes here in the
    // various blocks.
    let key_asn_1 = ASN1Block::Sequence(
        0,
        vec![
            ED_25519_ALG.clone(),
            // Length is expressed in bits.
            ASN1Block::BitString(0, key_bytes.len() * BITS_PER_BYTE, key_bytes.into()),
        ],
    );
    simple_asn1::to_der(&key_asn_1).context("Could not encode key to DER")
}

/// Decodes the public key as a binary DER-encoded `SubjectPublicKeyInfo` (see
/// https://tools.ietf.org/html/rfc5280#section-4.1).
pub fn decode_public_key_der(key_der: &[u8]) -> anyhow::Result<Vec<u8>> {
    let asn_blocks = simple_asn1::from_der(key_der).unwrap();
    if asn_blocks.len() != 1 {
        anyhow::bail!(
            "Invalid number of ASN.1 blocks: {}, expected: 1",
            asn_blocks.len()
        );
    }
    if let ASN1Block::Sequence(_, v) = &asn_blocks[0] {
        if v.len() != 2 {
            anyhow::bail!("Invalid length of ASN.1 sequence: {}, expected: 2", v.len());
        }
        if v[0] == ED_25519_ALG.clone() {
            if let ASN1Block::BitString(_, _, key_bytes) = &v[1] {
                Ok(key_bytes.clone())
            } else {
                anyhow::bail!("Invalid ASN.1 block: {:?}, expected: BIT STRING", v[1]);
            }
        } else {
            anyhow::bail!("Invalid algorithm: {:?}", v[0]);
        }
    } else {
        anyhow::bail!(
            "Invalid ASN.1 block: {:?}, expected: SEQUENCE",
            asn_blocks[0]
        );
    }
}

#[derive(Clone, Debug, Default)]
pub struct SignatureBundle {
    /// Public key as a binary DER-encoded `SubjectPublicKeyInfo` (see
    /// https://tools.ietf.org/html/rfc5280#section-4.1).
    pub public_key_der: Vec<u8>,
    pub signed_hash: Vec<u8>,
    pub hash: Vec<u8>,
}

impl SignatureBundle {
    /// Signs a SHA-256 hash of the `input` using `private_key`.
    pub fn create(input: &[u8], key_pair: &KeyPair) -> anyhow::Result<SignatureBundle> {
        let hash = get_sha256(input);
        Ok(SignatureBundle {
            public_key_der: key_pair.public_key_der()?,
            signed_hash: key_pair.sign(&hash),
            hash,
        })
    }

    /// Verifies the signature validity.
    pub fn verify(&self) -> anyhow::Result<()> {
        let public_key_bytes = decode_public_key_der(&self.public_key_der)?;
        let public_key = signature::UnparsedPublicKey::new(&signature::ED25519, &public_key_bytes);
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

    /// Parses public key, signature and SHA-256 hash encoded from a file using PEM format.
    /// https://tools.ietf.org/html/rfc1421
    pub fn from_pem_file(filename: &str) -> anyhow::Result<SignatureBundle> {
        let file =
            read(filename).with_context(|| format!("Couldn't read signature file {}", filename))?;
        Self::from_pem(file.as_slice())
    }

    /// Parses public key, signature and SHA-256 hash encoded using PEM format.
    /// https://tools.ietf.org/html/rfc1421
    pub fn from_pem(file: &[u8]) -> anyhow::Result<SignatureBundle> {
        let file_content: HashMap<String, Vec<u8>> = pem::parse_many(file)?
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
            public_key_der: public_key.to_vec(),
            signed_hash: signed_hash.to_vec(),
            hash: hash.to_vec(),
        })
    }

    pub fn to_pem_file(&self, filename: &str) -> anyhow::Result<()> {
        let public_key_pem = create_pem(PUBLIC_KEY_TAG, &self.public_key_der);
        let signature_pem = create_pem(SIGNATURE_TAG, &self.signed_hash);
        let hash_pem = create_pem(HASH_TAG, &self.hash);
        let encoded_signature = pem::encode_many(&[public_key_pem, signature_pem, hash_pem]);
        write(filename, &encoded_signature)
            .with_context(|| format!("Couldn't write signature file {}", filename))?;
        Ok(())
    }
}

impl From<ModuleSignature> for SignatureBundle {
    fn from(module_signature: ModuleSignature) -> Self {
        let public_key_der = module_signature.public_key;
        let signed_hash = module_signature.signed_hash;
        let hash = module_signature.module_hash;
        Self {
            public_key_der,
            signed_hash,
            hash,
        }
    }
}

impl From<SignatureBundle> for ModuleSignature {
    fn from(signature_bundle: SignatureBundle) -> Self {
        let public_key = signature_bundle.public_key_der;
        let signed_hash = signature_bundle.signed_hash;
        let module_hash = signature_bundle.hash;
        Self {
            public_key,
            signed_hash,
            module_hash,
        }
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
