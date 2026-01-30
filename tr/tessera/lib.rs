//
// Copyright 2026 The Project Oak Authors
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

//! Parses and verifies C2SP t-log proofs defined at
//! https://c2sp.org/tlog-proof.

#![no_std]

extern crate alloc;

use alloc::{
    boxed::Box,
    format,
    string::{String, ToString},
    vec::Vec,
};

use base64::{Engine, engine::general_purpose::STANDARD as B64};
use ed25519_dalek::{Signature, Verifier, VerifyingKey};
use oak_digest::Sha256;
use sha2::{Digest, Sha256 as Sha256Hasher};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum TLogProofError {
    #[error("invalid proof header")]
    InvalidHeader,
    #[error("invalid index format")]
    InvalidIndex,
    #[error("malformed checkpoint section")]
    MalformedCheckpoint,
    #[error("malformed signature")]
    MalformedSignature,
    #[error("malformed verifying key")]
    MalformedVerifyingKey,
    #[error("checkpoint origin mismatch: expected {0}, got {1}")]
    OriginMismatch(String, String),
    #[error("mismatch between signatures and verifying keys")]
    SignatureMismatch,
    #[error("signature verification failed")]
    SigVerify,
    #[error("root hash mismatch")]
    RootMismatch,
    #[error("malformed data")]
    Format(#[from] Box<dyn core::error::Error + Send + Sync>),
}

/// A signing key in note format.
#[derive(Debug, Clone)]
pub struct NoteSigningKey {
    pub raw: [u8; 32],
}

/// A verifying key for a checkpoint signature in note format.
#[derive(Debug, Clone)]
pub struct NoteVerifyingKey {
    pub origin: String,
    pub key_id_hint: [u8; 4],
    pub version: u8,
    pub raw: [u8; 32],
}

impl NoteVerifyingKey {
    /// Parses a verifying key in note format.
    ///
    /// Valid example input:
    /// ```text
    /// paic.google.com/log/0+609b8245+Ae74NkuIVBowBYu37xUJ5e3wf52bMPhW9e59idWfWR2j
    /// ```
    pub fn parse(serialized: &str) -> Result<Self, TLogProofError> {
        // There may be more plusses in the base64 encoded part.
        let parts: Vec<&str> = serialized.splitn(3, '+').collect();
        if parts.len() < 3 {
            return Err(TLogProofError::MalformedVerifyingKey);
        }
        #[allow(clippy::get_first)]
        let origin = parts.get(0).unwrap().to_string();
        let id_encoded = parts.get(1).unwrap();
        let key_encoded = parts.get(2).unwrap();
        let id_bytes =
            hex::decode(id_encoded).map_err(|_| TLogProofError::MalformedVerifyingKey)?;
        let key_bytes =
            B64.decode(key_encoded).map_err(|_| TLogProofError::MalformedVerifyingKey)?;
        if key_bytes.len() != 33 {
            return Err(TLogProofError::MalformedVerifyingKey);
        }
        let version = key_bytes[0];
        if version != 0x01 && version != 0x04 {
            return Err(TLogProofError::MalformedVerifyingKey);
        }
        let key_id_hint: [u8; 4] =
            id_bytes.as_slice().try_into().map_err(|_| TLogProofError::MalformedVerifyingKey)?;
        let raw: [u8; 32] =
            key_bytes[1..33].try_into().map_err(|_| TLogProofError::MalformedVerifyingKey)?;
        Ok(NoteVerifyingKey { origin, key_id_hint, version, raw })
    }

    pub fn verify(
        &self,
        signed_payload: &[u8],
        signature: &NoteSignature,
    ) -> Result<(), TLogProofError> {
        let vkey = VerifyingKey::from_bytes(&self.raw)
            .map_err(|_| TLogProofError::MalformedVerifyingKey)?;
        let sig = Signature::from_bytes(&signature.raw);
        vkey.verify(signed_payload, &sig).map_err(|_| TLogProofError::SigVerify)?;
        Ok(())
    }
}

/// A signature on a checkpoint in note format.
#[derive(Debug, Clone)]
pub struct NoteSignature {
    pub origin: String,
    pub key_id_hint: [u8; 4],
    pub timestamp: u64,
    pub raw: [u8; 64],
}

impl NoteSignature {
    /// Parses a signature line from a C2SP t-log proof.
    ///
    /// Valid example input:
    /// ```text
    /// — paic.google.com/log/0 YJuCRffzjw85Wjrgi2alFJT94ZC97L+PYMnBPs4q/pN8y/h5Q3lyUfILQCS7bA6xgc/1CaX+T/yRXNhIIJbqvsjR4wU=
    /// ```
    pub fn parse(serialized: &str) -> Result<NoteSignature, TLogProofError> {
        let strip = serialized.strip_prefix("— ").ok_or(TLogProofError::MalformedSignature)?;
        let (origin, encoded) = strip.split_once(' ').ok_or(TLogProofError::MalformedSignature)?;
        let b = B64.decode(encoded).map_err(|e| TLogProofError::Format(Box::new(e)))?;
        // Since there is no type encoding, we use the length to distinguish
        // between main and co-signature.
        match b.len() {
            // Main signature, see https://c2sp.org/signed-note.
            68 => Ok(NoteSignature {
                origin: origin.to_string(),
                key_id_hint: b[0..4].try_into().unwrap(),
                timestamp: 0,
                raw: b[4..68].try_into().unwrap(),
            }),
            // Witness signature, see https://c2sp.org/tlog-cosignature.
            76 => Ok(NoteSignature {
                origin: origin.to_string(),
                key_id_hint: b[0..4].try_into().unwrap(),
                timestamp: u64::from_be_bytes(b[4..12].try_into().unwrap()),
                raw: b[12..76].try_into().unwrap(),
            }),
            _ => Err(TLogProofError::MalformedSignature),
        }
    }
}

/// Represents the checkpoint section of a t-log proof.
#[derive(Debug, Clone)]
pub struct Checkpoint {
    pub origin: String,
    pub tree_size: u64,
    pub root_hash: Sha256,

    /// The full text of the checkpoint that is signed. Includes origin, size,
    /// root hash, and any extra data.
    pub signed_payload: String,

    // Main signature and signatures from witnesses in no particular order.
    pub signatures: Vec<NoteSignature>,
}

impl Checkpoint {
    /// Parses the checkpoint section of a t-log proof.
    pub fn parse(serialized: &str) -> Result<Self, TLogProofError> {
        let mut lines = serialized.lines();
        // Read the checkpoint body.
        let origin = lines.next().ok_or(TLogProofError::MalformedCheckpoint)?;
        let cp_size_str = lines.next().ok_or(TLogProofError::MalformedCheckpoint)?;
        let tree_size: u64 =
            cp_size_str.parse().map_err(|_| TLogProofError::MalformedCheckpoint)?;
        let cp_root_str = lines.next().ok_or(TLogProofError::MalformedCheckpoint)?;
        let root_hash_raw =
            B64.decode(cp_root_str).map_err(|_| TLogProofError::MalformedCheckpoint)?;
        let root_hash = Sha256::from(
            <[u8; 32]>::try_from(root_hash_raw).map_err(|_| TLogProofError::MalformedCheckpoint)?,
        );
        let signed_payload = format!("{}\n{}\n{}\n", origin, cp_size_str, cp_root_str);

        let mut signatures = Vec::new();
        for line in lines {
            if line.is_empty() {
                continue;
            }
            // If it doesn't start with "— ", then it is part of the
            // checkpoint's extra data. Such extra data would be part of
            // the signed payload. We ignore extra data.
            signatures.push(NoteSignature::parse(line)?);
        }

        Ok(Checkpoint {
            origin: origin.to_string(),
            tree_size,
            root_hash,
            signed_payload,
            signatures,
        })
    }
}

/// A C2SP t-log proof bundle.
#[derive(Debug, Clone)]
pub struct TLogProof {
    pub index: u64,
    pub proof_hashes: Vec<Sha256>,
    pub checkpoint: Checkpoint,
}

impl TLogProof {
    /// Parses a C2SP t-log proof bundle from its textual representation.
    pub fn parse(serialized: &str) -> Result<Self, TLogProofError> {
        let mut lines = serialized.lines();

        // Check the header.
        if lines.next() != Some("c2sp.org/tlog-proof@v1") {
            return Err(TLogProofError::InvalidHeader);
        }

        // Skip over optional extra data.
        let mut line = lines.next().ok_or(TLogProofError::InvalidIndex)?;
        if line.starts_with("extra ") {
            line = lines.next().ok_or(TLogProofError::InvalidIndex)?;
        }

        // Parse the index number.
        let index: u64 = line
            .strip_prefix("index ")
            .ok_or(TLogProofError::InvalidIndex)?
            .parse()
            .map_err(|e| TLogProofError::Format(Box::new(e)))?;

        // Read the inclusion proof hashes, until empty line.
        let mut proof_hashes = Vec::new();
        for line in lines.by_ref() {
            if line.is_empty() {
                break;
            }
            let bytes = B64.decode(line).map_err(|e| TLogProofError::Format(Box::new(e)))?;
            proof_hashes.push(Sha256::from(
                <[u8; 32]>::try_from(bytes).map_err(|_| TLogProofError::RootMismatch)?,
            ));
        }

        // Read the checkpoint body.
        let checkpoint_str = lines.collect::<Vec<_>>().join("\n");
        let checkpoint = Checkpoint::parse(&checkpoint_str)?;

        Ok(TLogProof { index, proof_hashes, checkpoint })
    }

    /// Verifies a C2SP tlog-proof bundle.
    ///
    /// # Arguments
    ///
    /// * `origin`: The expected log origin (e.g., "example.com/log").
    /// * `verifying_keys`: Verifying keys for log and witnesses, in arbitrary
    ///   order. The t-log proof must contain signatures for all of these keys.
    ///   It is fine to specify a subset only as long as a verifying key for the
    ///   main signature is present.
    /// * `entry`: The raw bytes of the entry or leaf that was logged.
    pub fn verify(
        &self,
        origin: &str,
        verifying_keys: &[NoteVerifyingKey],
        entry: &[u8],
    ) -> Result<(), TLogProofError> {
        // Verify origin.
        if self.checkpoint.origin != origin {
            return Err(TLogProofError::OriginMismatch(
                origin.into(),
                self.checkpoint.origin.clone(),
            ));
        }

        // Verify signatures.
        let mut main_sig_found: usize = 0;
        for vkey in verifying_keys {
            let mut num_found: usize = 0;
            for sig in &self.checkpoint.signatures {
                if sig.origin == vkey.origin {
                    // If the signature contains a timestamp then it is a
                    // witness signature. For details see
                    // https://c2sp.org/tlog-cosignature.
                    if sig.timestamp > 0 {
                        let payload = format!(
                            "cosignature/v1\ntime {}\n{}",
                            sig.timestamp, self.checkpoint.signed_payload
                        );
                        vkey.verify(payload.as_bytes(), sig)?;
                    } else {
                        // Standard log signature.
                        vkey.verify(self.checkpoint.signed_payload.as_bytes(), sig)?;
                    }

                    num_found += 1;
                    if vkey.origin == origin {
                        main_sig_found += 1;
                    }
                }
            }
            if num_found != 1 {
                return Err(TLogProofError::SignatureMismatch);
            }
        }
        if main_sig_found != 1 {
            return Err(TLogProofError::SignatureMismatch);
        }

        // Verify Merkle inclusion.
        let mut index = self.index;
        let mut hash =
            Sha256Hasher::new().chain_update([0x00]).chain_update(entry).finalize().to_vec();
        for sibling in &self.proof_hashes {
            let mut h = Sha256Hasher::new().chain_update([0x01]);
            if index & 1 == 0 {
                h.update(&hash);
                h.update(sibling);
            } else {
                h.update(sibling);
                h.update(&hash);
            }
            hash = h.finalize().to_vec();
            index >>= 1;
        }
        if hash != self.checkpoint.root_hash.as_ref() {
            return Err(TLogProofError::RootMismatch);
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use base64::{Engine, engine::general_purpose::STANDARD as B64};
    use ed25519_dalek::{Signer, SigningKey};
    use sha2::{Digest, Sha256 as Sha256Hasher};

    use super::*;

    const FAKE_ORIGIN: &str = "example.com/log";
    const TEST_TLOG_PROOF: &str = include_str!("testdata/test.tlog-proof");
    const TEST_ENTRY: &[u8] = b"test entry data";
    const TEST_MAIN_VKEY: &str =
        "fake.log.origin/log+527eabb8+AddT9PtBhhNAsDYZ0V0euiRbXuvrLsw4L6vKARfipnmz";
    const TEST_WITNESS_VKEY: &str =
        "test-witness+26349ef0+BIQDFTUlktisMqJzWn8qhteWrRr4dLcQ9R37T+8LQyQF";

    struct ReferenceValues {
        origin: String,
        signing_key: Option<NoteSigningKey>,
        verifying_key: NoteVerifyingKey,
    }

    impl ReferenceValues {
        fn make_test_example() -> Self {
            let verifying_key =
                NoteVerifyingKey::parse(TEST_MAIN_VKEY).expect("failed to parse verifying key");
            Self { origin: verifying_key.origin.clone(), signing_key: None, verifying_key }
        }

        fn make_fake_example() -> Self {
            let signing_key = NoteSigningKey { raw: [42u8; 32] };
            let s = SigningKey::from_bytes(&signing_key.raw);
            let verifying_key = NoteVerifyingKey {
                origin: FAKE_ORIGIN.into(),
                key_id_hint: [99u8; 4], // Incorrect, but good enough.
                version: 0,
                raw: s.verifying_key().to_bytes(),
            };
            Self { origin: FAKE_ORIGIN.into(), signing_key: Some(signing_key), verifying_key }
        }

        /// Imitates the main t-log signature.
        fn sign(&self, msg: &str) -> NoteSignature {
            let signing_key = SigningKey::from_bytes(&self.signing_key.as_ref().unwrap().raw);
            let signature = signing_key.sign(msg.as_bytes());
            NoteSignature {
                origin: self.origin.clone(),
                key_id_hint: self.verifying_key.key_id_hint,
                timestamp: 0,
                raw: signature.to_bytes(),
            }
        }
    }

    fn hash_leaf(data: &[u8]) -> Sha256 {
        let mut hasher = Sha256Hasher::new();
        hasher.update([0x00]);
        hasher.update(data);
        Sha256::from(<[u8; 32]>::from(hasher.finalize()))
    }

    fn hash_node(left: &Sha256, right: &Sha256) -> Sha256 {
        let mut hasher = Sha256Hasher::new();
        hasher.update([0x01]);
        hasher.update(left);
        hasher.update(right);
        Sha256::from(<[u8; 32]>::from(hasher.finalize()))
    }

    /// Creates a tree of size 2 where our entry is at index 0.
    fn make_tree_size_2(entry: &[u8]) -> (Sha256, Sha256) {
        let sibling_hash = Sha256::from([0xAA; 32]);
        let leaf = hash_leaf(entry);
        let root = hash_node(&leaf, &sibling_hash);
        (root, sibling_hash)
    }

    fn make_checkpoint(
        rvalues: &ReferenceValues,
        tree_size: u64,
        root_hash: &Sha256,
    ) -> Checkpoint {
        let root_b64 = B64.encode(root_hash);
        let signed_payload = format!("{}\n{}\n{}\n", rvalues.origin, tree_size, root_b64);
        let sig = rvalues.sign(&signed_payload);
        Checkpoint {
            origin: rvalues.origin.clone(),
            tree_size,
            root_hash: *root_hash,
            signed_payload,
            signatures: vec![sig],
        }
    }

    fn make_proof(index: u64, proof_hashes: &[Sha256], checkpoint: &Checkpoint) -> String {
        let hashes_str = proof_hashes.iter().map(|h| B64.encode(h)).collect::<Vec<_>>().join("\n");

        let mut sigs_str = String::new();
        for sig in &checkpoint.signatures {
            let mut sig_bytes = Vec::new();
            sig_bytes.extend_from_slice(&sig.key_id_hint);
            if sig.timestamp != 0 {
                sig_bytes.extend_from_slice(&sig.timestamp.to_be_bytes());
            }
            sig_bytes.extend_from_slice(&sig.raw);
            let sig_b64 = B64.encode(sig_bytes);
            sigs_str.push_str(&format!("— {} {}\n", sig.origin, sig_b64));
        }

        format!(
            "c2sp.org/tlog-proof@v1\n\
             index {}\n\
             {}\n\
             \n\
             {}{}",
            index, hashes_str, checkpoint.signed_payload, sigs_str
        )
    }

    #[test]
    fn test_parse_test_example_success() {
        let rvalues = ReferenceValues::make_test_example();

        let proof = TLogProof::parse(TEST_TLOG_PROOF).expect("failed to parse proof");

        assert_eq!(proof.index, 3);
        assert_eq!(proof.proof_hashes.len(), 2);
        assert_eq!(proof.checkpoint.origin, rvalues.origin);
        assert_eq!(proof.checkpoint.tree_size, 4);
        assert_eq!(proof.checkpoint.signatures.len(), 2);
        assert_eq!(proof.checkpoint.signatures[0].origin, rvalues.origin);
    }

    #[test]
    fn test_parse_fake_example_success() {
        let rvalues = ReferenceValues::make_fake_example();
        let root_hash = Sha256::from([0xCC; 32]);
        let checkpoint = make_checkpoint(&rvalues, 456, &root_hash);
        let proof_str = make_proof(123, &[Sha256::from([0xAA; 32])], &checkpoint);

        let proof = TLogProof::parse(&proof_str).expect("failed to parse proof");

        assert_eq!(proof.index, 123);
        assert_eq!(proof.proof_hashes.len(), 1);
        assert_eq!(proof.checkpoint.origin, rvalues.origin);
        assert_eq!(proof.checkpoint.tree_size, 456);
        assert_eq!(proof.checkpoint.root_hash, root_hash);
        assert_eq!(proof.checkpoint.signatures.len(), 1);
        assert_eq!(proof.checkpoint.signatures[0].origin, rvalues.origin);
    }

    #[test]
    fn test_parse_invalid_header_failure() {
        let proof_str = "invalid-header\nindex 0\n";

        let result = TLogProof::parse(proof_str);

        assert!(matches!(result, Err(TLogProofError::InvalidHeader)));
    }

    #[test]
    fn test_verify_test_example_success() {
        let rvalues = ReferenceValues::make_test_example();
        let proof = TLogProof::parse(TEST_TLOG_PROOF).unwrap();
        let witness_vkey = NoteVerifyingKey::parse(TEST_WITNESS_VKEY).unwrap();

        let result =
            proof.verify(&rvalues.origin, &[rvalues.verifying_key, witness_vkey], TEST_ENTRY);

        assert!(result.is_ok());
    }

    #[test]
    fn test_verify_fake_example_success() {
        let rvalues = ReferenceValues::make_fake_example();
        let entry = b"valid-entry";
        let (root, sibling) = make_tree_size_2(entry);
        let checkpoint = make_checkpoint(&rvalues, 2, &root);
        let proof_str = make_proof(0, &[sibling], &checkpoint);

        let proof = TLogProof::parse(&proof_str).unwrap();

        assert!(proof.verify(&rvalues.origin, &[rvalues.verifying_key], entry).is_ok());
    }

    #[test]
    fn test_verify_wrong_entry_failure() {
        let rvalues = ReferenceValues::make_fake_example();
        let entry = b"real-entry";
        let (root, sibling) = make_tree_size_2(entry);
        let checkpoint = make_checkpoint(&rvalues, 2, &root);
        let proof_str = make_proof(0, &[sibling], &checkpoint);
        let proof = TLogProof::parse(&proof_str).unwrap();

        let result = proof.verify(&rvalues.origin, &[rvalues.verifying_key], b"fake-entry");

        assert!(matches!(result, Err(TLogProofError::RootMismatch)));
    }

    #[test]
    fn test_verify_tampered_signature_failure() {
        let rvalues = ReferenceValues::make_fake_example();
        let entry = b"data";
        let (root, sibling) = make_tree_size_2(entry);
        let checkpoint = make_checkpoint(&rvalues, 2, &root);
        let mut proof_str = make_proof(0, &[sibling], &checkpoint);
        let parts: Vec<&str> = proof_str.split("— ").collect();
        let bad_sig = B64.encode([0xBB; 68]);
        proof_str = format!("{}— {} {}", parts[0], rvalues.origin, bad_sig);
        let proof = TLogProof::parse(&proof_str).unwrap();

        let result = proof.verify(&rvalues.origin, &[rvalues.verifying_key], entry);

        assert!(matches!(result, Err(TLogProofError::SigVerify)));
    }

    #[test]
    fn test_verify_wrong_origin_failure() {
        let rvalues = ReferenceValues::make_fake_example();
        let entry = b"data";
        let (root, sibling) = make_tree_size_2(entry);
        let checkpoint = make_checkpoint(&rvalues, 2, &root);
        let proof_str = make_proof(0, &[sibling], &checkpoint);
        let proof = TLogProof::parse(&proof_str).unwrap();

        let result = proof.verify("wrong.com/log", &[rvalues.verifying_key], entry);

        assert!(matches!(result, Err(TLogProofError::OriginMismatch(..))));
    }
}
