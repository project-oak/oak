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

//! Parses and verifies [C2SP t-log proofs](https://c2sp.org/tlog-proof).
//!
//! A t-log proof bundles an inclusion proof, a signed
//! [checkpoint](https://c2sp.org/tlog-checkpoint), and optional witness
//! [cosignatures](https://c2sp.org/tlog-cosignature) into a single
//! offline-verifiable artifact attesting that an entry was logged.
//!
//! # Usage
//!
//! ```
//! let policy = policy::Policy::parse("log example.com/log+abcd1234+A...\nquorum none\n")?;
//! let proof = TLogProof::parse(&proof_text)?;
//! proof.verify(&policy, &entry_bytes)?;
//! ```
//!
//! Signature verification supports Ed25519 (type 0x01), timestamped
//! Ed25519 witness cosignatures (type 0x04), and timestamped ML-DSA-44
//! signatures (type 0x06) as defined by the
//! [signed-note specification](https://c2sp.org/signed-note#signature-types)
//! and the
//! [tlog-cosignature specification](https://c2sp.org/tlog-cosignature).
//!
//! ML-DSA-44 (type 0x06) may be used by both logs and witnesses.

#![no_std]

extern crate alloc;

pub mod note;
pub mod policy;

use alloc::{
    boxed::Box,
    format,
    string::{String, ToString},
    vec::Vec,
};

use base64::{Engine, engine::general_purpose::STANDARD as B64};
pub use note::{
    NoteError, NoteSignature, NoteSigningKey, NoteVerifyingKey, SignatureType, SigningKey,
    VerifyingKey,
};
use oak_digest::Sha256;
pub use policy::{Policy, PolicyError};
use rs_merkle::Hasher;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum TLogProofError {
    #[error("invalid proof header")]
    InvalidHeader,
    #[error("invalid index format")]
    InvalidIndex,
    #[error("malformed checkpoint")]
    MalformedCheckpoint(#[from] CheckpointError),
    #[error("malformed proof")]
    MalformedProof,
    #[error("mismatch between signatures and verifying keys")]
    SignatureMismatch,
    #[error("root hash mismatch")]
    RootMismatch,
    #[error("invalid Merkle chain")]
    InvalidMerkleChain,
    #[error("witness quorum not satisfied")]
    InsufficientWitnesses,
    #[error(transparent)]
    Note(#[from] NoteError),
    #[error("malformed data")]
    Format(#[from] Box<dyn core::error::Error + Send + Sync>),
}

/// Errors produced when parsing a checkpoint body.
#[derive(Error, Debug)]
pub enum CheckpointError {
    #[error("malformed checkpoint")]
    Malformed,
}

/// Represents the checkpoint section of a t-log proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Checkpoint {
    pub origin: String,
    pub tree_size: u64,
    pub root_hash: Sha256,

    /// The full text of the checkpoint body that is signed. Includes origin,
    /// size, root hash, and any extension lines.
    pub signed_payload: String,

    /// Main signature and signatures from witnesses in no particular order.
    pub signatures: Vec<NoteSignature>,
}

impl Checkpoint {
    /// Parses the checkpoint section of a t-log proof.
    ///
    /// The checkpoint body consists of origin, tree size, base64-encoded root
    /// hash, and optional extension lines, followed by a blank separator line
    /// and then signature lines.
    pub fn parse(serialized: &str) -> Result<Self, CheckpointError> {
        let mut lines = serialized.lines();

        // Read the required checkpoint body fields.
        let origin = lines.next().ok_or(CheckpointError::Malformed)?;
        let cp_size_str = lines.next().ok_or(CheckpointError::Malformed)?;
        let tree_size: u64 = cp_size_str.parse().map_err(|_| CheckpointError::Malformed)?;
        let cp_root_str = lines.next().ok_or(CheckpointError::Malformed)?;
        let root_hash_raw = B64.decode(cp_root_str).map_err(|_| CheckpointError::Malformed)?;
        let root_hash = Sha256::from(
            <[u8; 32]>::try_from(root_hash_raw).map_err(|_| CheckpointError::Malformed)?,
        );

        // Build signed payload from the body: the three required fields plus
        // any extension lines, up to the blank separator.
        let mut signed_payload = format!("{}\n{}\n{}\n", origin, cp_size_str, cp_root_str);
        for line in lines.by_ref() {
            if line.is_empty() {
                break;
            }
            signed_payload.push_str(line);
            signed_payload.push('\n');
        }

        // Parse signature lines after the blank separator.
        let mut signatures = Vec::new();
        for line in lines {
            if line.is_empty() {
                continue;
            }
            signatures.push(NoteSignature::parse(line).map_err(|_| CheckpointError::Malformed)?);
        }

        Ok(Checkpoint {
            origin: origin.to_string(),
            tree_size,
            root_hash,
            signed_payload,
            signatures,
        })
    }

    /// Serialises this checkpoint to its textual representation.
    ///
    /// The output is the signed payload (which includes any extension lines)
    /// followed by a blank line and the signature lines.
    pub fn serialize(&self) -> String {
        let mut s = String::new();
        // signed_payload already ends with '\n'.
        s.push_str(&self.signed_payload);
        // Blank line separating body from signatures.
        s.push('\n');
        for sig in &self.signatures {
            s.push_str(&sig.to_signature_line());
            s.push('\n');
        }
        s
    }
}

/// A C2SP t-log proof bundle.
#[derive(Debug, Clone, PartialEq, Eq)]
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
            let bytes = B64.decode(line).map_err(|_| TLogProofError::MalformedProof)?;
            proof_hashes.push(Sha256::from(
                <[u8; 32]>::try_from(bytes).map_err(|_| TLogProofError::MalformedProof)?,
            ));
        }

        // Read the checkpoint body.
        let checkpoint_str = lines.collect::<Vec<_>>().join("\n");
        let checkpoint = Checkpoint::parse(&checkpoint_str)?;

        Ok(TLogProof { index, proof_hashes, checkpoint })
    }

    /// Serialises this proof to the
    /// [C2SP tlog-proof](https://c2sp.org/tlog-proof) text format.
    pub fn serialize(&self) -> String {
        let mut s = String::new();
        s.push_str("c2sp.org/tlog-proof@v1\n");
        s.push_str(&format!("index {}\n", self.index));
        for hash in &self.proof_hashes {
            s.push_str(&B64.encode(hash));
            s.push('\n');
        }
        // Blank line separating proof hashes from checkpoint.
        s.push('\n');
        s.push_str(&self.checkpoint.serialize());
        s
    }

    /// Verifies a C2SP tlog-proof bundle against a [`Policy`].
    ///
    /// # Arguments
    ///
    /// * `policy`: The sigsum policy specifying trusted log keys and witness
    ///   quorum. The t-log proof must contain exactly one valid signature from
    ///   one of the policy's log keys, and enough witness cosignatures to
    ///   satisfy the quorum.
    /// * `entry`: The raw bytes of the entry or leaf that was logged.
    pub fn verify(&self, policy: &policy::Policy, entry: &[u8]) -> Result<(), TLogProofError> {
        // Verify log signature: exactly one trusted log key must match and
        // verify exactly one signature in the checkpoint.
        let mut num_found: usize = 0;
        for log_key in policy.log_keys() {
            if self.checkpoint.origin != log_key.origin {
                continue;
            }
            // Verify log signature.
            for sig in &self.checkpoint.signatures {
                if sig.matches_key(log_key) {
                    log_key.verify(&self.checkpoint.signed_payload, sig)?;
                    num_found += 1;
                }
            }
        }
        if num_found != 1 {
            return Err(TLogProofError::SignatureMismatch);
        }

        // Verify witness cosignatures and check quorum.
        let mut verified_witnesses: Vec<&NoteVerifyingKey> = Vec::new();
        for sig in &self.checkpoint.signatures {
            for witness_key in policy.witness_keys() {
                if sig.matches_key(witness_key)
                    && witness_key.verify(&self.checkpoint.signed_payload, sig).is_ok()
                {
                    verified_witnesses.push(witness_key);
                    break;
                }
            }
        }
        if !policy.check_quorum(&verified_witnesses) {
            return Err(TLogProofError::InsufficientWitnesses);
        }

        // Verify Merkle inclusion.
        let hash = self.compute_root_hash(entry)?;
        if hash != self.checkpoint.root_hash {
            return Err(TLogProofError::RootMismatch);
        }

        Ok(())
    }

    /// Computes the Merkle root hash from the proof hashes and the given entry.
    fn compute_root_hash(&self, entry: &[u8]) -> Result<Sha256, TLogProofError> {
        let tree_size = self.checkpoint.tree_size;
        let leaf_index = self.index;
        if leaf_index >= tree_size {
            return Err(TLogProofError::InvalidMerkleChain);
        }

        let leaf_hash = C2spHasher::hash(entry);
        let merkle_proof = rs_merkle::MerkleProof::<C2spHasher>::new(self.proof_hashes.clone());
        let root = merkle_proof
            .root(&[leaf_index as usize], &[leaf_hash], tree_size as usize)
            .map_err(|_| TLogProofError::InvalidMerkleChain)?;
        Ok(root)
    }
}

impl TryFrom<&Vec<u8>> for TLogProof {
    type Error = TLogProofError;

    fn try_from(bytes: &Vec<u8>) -> Result<Self, Self::Error> {
        let s = core::str::from_utf8(bytes.as_slice())
            .map_err(|e| TLogProofError::Format(Box::new(e)))?;
        Self::parse(s)
    }
}

/// A C2SP/RFC 6962 compatible hasher for rs_merkle.
#[derive(Clone)]
struct C2spHasher;

impl Hasher for C2spHasher {
    type Hash = Sha256;

    fn hash(data: &[u8]) -> Self::Hash {
        // Leaf hash: SHA256(0x00 || data)
        let mut buf = alloc::vec::Vec::with_capacity(1 + data.len());
        buf.push(0x00);
        buf.extend_from_slice(data);
        Sha256::from_contents(&buf)
    }

    fn concat_and_hash(left: &Self::Hash, right: Option<&Self::Hash>) -> Self::Hash {
        match right {
            // Node hash: SHA256(0x01 || left || right)
            Some(right_hash) => {
                let mut buf = [0u8; 65];
                buf[0] = 0x01;
                buf[1..33].copy_from_slice(left.as_ref());
                buf[33..65].copy_from_slice(right_hash.as_ref());
                Sha256::from_contents(&buf)
            }
            // Promote the left child if there is no right child.
            None => *left,
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use base64::{Engine, engine::general_purpose::STANDARD as B64};
    use oak_crypto_tink::ml_dsa_44;
    use oak_time::Instant;

    use super::*;
    use crate::note::NoteError;

    const FAKE_ORIGIN: &str = "example.com/log";
    const TEST_TLOG_PROOF: &str = include_str!("testdata/test.tlog-proof");
    const TEST_ENTRY: &[u8] = b"test entry data";
    const TEST_MAIN_VKEY: &str =
        "fake.log.origin/log+527eabb8+AddT9PtBhhNAsDYZ0V0euiRbXuvrLsw4L6vKARfipnmz";
    const TEST_WITNESS_VKEY: &str =
        "test-witness+26349ef0+BIQDFTUlktisMqJzWn8qhteWrRr4dLcQ9R37T+8LQyQF";

    const TEST_REAL_ENTRY: &[u8] = b"hello tesseroak\n";
    const TEST_REAL_PROOF_HASHES: &[&str] = &[
        "fGRlLyuz+L9Jb8+uTSut/2aVc4z7fKFW+clvsb6xjEM=",
        "F6LautOHD5eppkWC0xn/lz00X5g2yLlZAkl2jCI/wdE=",
        "qH7OJxFNup+TDvJuohd2HphKVngfMeMzUK8QChEDcas=",
        "+Y3g758yXtPCRh/eqhLTA3bdcx+cCV1Uah0JdgB0YEs=",
        "vq8cJSjj8dPVmFBRUqDLlaMqW6aAYR2GKugVhgudXLs=",
        "J0z3X5qTb9WFC1gABhVFx0bW1rVZRL+DAoBL2e2h4G4=",
        "NmSbYg25xNFzTRerIsF3HbEMyTIDqW87AQd9ekzopE8=",
        "L8BZipjURnkctkjJtGJs+YyTXMssvNKA7+a8nV2JT/s=",
        "pva4RFzCejMkVMVmYc93As2lbk7WAyrw58TvrzEOjNc=",
    ];
    const TEST_REAL_ROOT_HASH: &str = "QYfrD7XAd4qUHbRBs4dDyDZwpZN4M/cccXr2G56pxkY=";

    /// A test identity bundling a signing key, verifying key, and origin.
    struct TestIdentity {
        origin: String,
        signing_key: Option<NoteSigningKey>,
        verifying_key: NoteVerifyingKey,
    }

    impl TestIdentity {
        /// Creates an identity from the real test-vector verifying key (no
        /// signing capability).
        fn real_ed25519() -> Self {
            let verifying_key =
                NoteVerifyingKey::parse(TEST_MAIN_VKEY).expect("parsing verifying key");
            Self { origin: verifying_key.origin.clone(), signing_key: None, verifying_key }
        }

        /// Deterministic fake Ed25519 log identity.
        fn fake_ed25519() -> Self {
            Self::ed25519(FAKE_ORIGIN, [42u8; 32])
        }

        /// Deterministic fake Ed25519CosignatureV1 witness identity.
        fn fake_cosignature_v1() -> Self {
            Self::cosignature_v1("fake-witness", [43u8; 32])
        }

        /// Fake MlDsa44SubtreeV1 identity.
        fn fake_subtree_v1() -> Self {
            Self::subtree_v1("fake-ml-dsa-witness")
        }

        fn ed25519(origin: &str, raw: [u8; 32]) -> Self {
            let note_key = NoteSigningKey::new(
                origin,
                SigningKey::Ed25519(ed25519_dalek::SigningKey::from_bytes(&raw)),
            );
            let verifying_key = note_key.verifying_key();
            Self { origin: origin.into(), signing_key: Some(note_key), verifying_key }
        }

        fn cosignature_v1(origin: &str, raw: [u8; 32]) -> Self {
            let note_key = NoteSigningKey::new(
                origin,
                SigningKey::Ed25519CosignatureV1(ed25519_dalek::SigningKey::from_bytes(&raw)),
            );
            let verifying_key = note_key.verifying_key();
            Self { origin: origin.into(), signing_key: Some(note_key), verifying_key }
        }

        fn subtree_v1(origin: &str) -> Self {
            let kp = ml_dsa_44::generate_key_pair().expect("generating ML-DSA-44 key pair");
            let note_key = NoteSigningKey::new(origin, SigningKey::MlDsa44SubtreeV1(kp));
            let verifying_key = note_key.verifying_key();
            Self { origin: origin.into(), signing_key: Some(note_key), verifying_key }
        }

        /// Signs a checkpoint, dispatching based on the key's signature type.
        fn sign(&self, checkpoint_text: &str, timestamp: Instant) -> NoteSignature {
            self.signing_key.as_ref().unwrap().sign(checkpoint_text, timestamp).unwrap()
        }

        /// Returns a policy text line for this identity's vkey.
        fn log_line(&self) -> String {
            format!("log {}\n", self.verifying_key.to_vkey_string())
        }
    }

    /// Helper for building Merkle trees with a known entry at a given index.
    struct TestTree {
        leaves: Vec<Sha256>,
        tree: rs_merkle::MerkleTree<C2spHasher>,
    }

    impl TestTree {
        /// Returns a tree with `size` leaves, where the leaf at `entry_index`
        /// is `entry` and all other leaves are unique fillers.
        fn new(size: usize, entry_index: usize, entry: &[u8]) -> Self {
            let mut leaves = vec![Sha256::from([0; 32]); size];
            for (i, leaf) in leaves.iter_mut().enumerate().take(size) {
                if i == entry_index {
                    *leaf = C2spHasher::hash(entry);
                } else {
                    let mut data = [0u8; 32];
                    data[0..8].copy_from_slice(&(i as u64).to_le_bytes());
                    *leaf = C2spHasher::hash(&data);
                }
            }
            let tree = rs_merkle::MerkleTree::<C2spHasher>::from_leaves(&leaves);
            Self { leaves, tree }
        }

        fn root(&self) -> Sha256 {
            self.tree.root().unwrap_or(Sha256::from([0; 32]))
        }

        fn proof(&self, index: usize) -> Vec<Sha256> {
            if self.leaves.is_empty() {
                return Vec::new();
            }
            self.tree.proof(&[index]).proof_hashes().to_vec()
        }
    }

    /// Builds a checkpoint with an Ed25519 log signature.
    fn make_checkpoint(identity: &TestIdentity, tree_size: u64, root_hash: &Sha256) -> Checkpoint {
        let root_b64 = B64.encode(root_hash);
        let signed_payload = format!("{}\n{}\n{}\n", identity.origin, tree_size, root_b64);
        let sig = identity.sign(&signed_payload, Instant::UNIX_EPOCH);
        Checkpoint {
            origin: identity.origin.clone(),
            tree_size,
            root_hash: *root_hash,
            signed_payload,
            signatures: vec![sig],
        }
    }

    /// Serialises a tlog proof bundle to its text format.
    fn make_tlog_proof(index: u64, proof_hashes: &[Sha256], checkpoint: &Checkpoint) -> String {
        let mut sigs_str = String::new();
        for sig in &checkpoint.signatures {
            let mut sig_bytes = Vec::new();
            sig_bytes.extend_from_slice(&sig.key_id_hint);
            sig_bytes.extend_from_slice(&sig.sig_bytes);
            let sig_b64 = B64.encode(sig_bytes);
            sigs_str.push_str(&format!("— {} {}\n", sig.origin, sig_b64));
        }

        let mut result = format!("c2sp.org/tlog-proof@v1\nindex {}\n", index);
        for hash in proof_hashes {
            result.push_str(&B64.encode(hash));
            result.push('\n');
        }
        // Blank line separating proof hashes from checkpoint.
        result.push('\n');
        // Checkpoint body (signed_payload ends with \n).
        result.push_str(&checkpoint.signed_payload);
        // Blank line separating checkpoint body from signatures.
        result.push('\n');
        result.push_str(&sigs_str);
        result
    }

    #[test]
    fn test_verify_ed25519_wrong_key() {
        let signer = TestIdentity::fake_ed25519();
        let other = TestIdentity::ed25519(FAKE_ORIGIN, [99u8; 32]);
        let signed_text = "test message\n";
        let sig = signer.sign(signed_text, Instant::UNIX_EPOCH);

        let result = other.verifying_key.verify(signed_text, &sig);
        assert!(matches!(result, Err(NoteError::SignatureVerificationFailed)));
    }

    #[test]
    fn test_parse_checkpoint_valid() {
        let root = Sha256::from([0xAA; 32]);
        let root_b64 = B64.encode(root);
        let checkpoint_str = format!("example.com/log\n42\n{}\n\n", root_b64);

        let cp = Checkpoint::parse(&checkpoint_str).unwrap();

        assert_eq!(cp.origin, "example.com/log");
        assert_eq!(cp.tree_size, 42);
        assert_eq!(cp.root_hash, root);
        assert!(cp.signatures.is_empty());
    }

    #[test]
    fn test_parse_checkpoint_with_extension_lines() {
        let root = Sha256::from([0xBB; 32]);
        let root_b64 = B64.encode(root);
        let checkpoint_str =
            format!("example.com/log\n10\n{}\nextra-line-1\nextra-line-2\n\n", root_b64);

        let cp = Checkpoint::parse(&checkpoint_str).unwrap();

        assert_eq!(cp.tree_size, 10);
        let expected_payload =
            format!("example.com/log\n10\n{}\nextra-line-1\nextra-line-2\n", root_b64);
        assert_eq!(cp.signed_payload, expected_payload);
    }

    #[test]
    fn test_parse_checkpoint_missing_fields() {
        assert!(matches!(Checkpoint::parse("single-line"), Err(CheckpointError::Malformed)));
    }

    #[test]
    fn test_parse_checkpoint_invalid_tree_size() {
        let checkpoint_str = "origin\nnot_a_number\nhash\n\n";
        assert!(matches!(Checkpoint::parse(checkpoint_str), Err(CheckpointError::Malformed)));
    }

    #[test]
    fn test_parse_checkpoint_invalid_root_hash() {
        let checkpoint_str = "origin\n1\nnot_base64!\n\n";
        assert!(matches!(Checkpoint::parse(checkpoint_str), Err(CheckpointError::Malformed)));
    }

    #[test]
    fn test_parse_proof_real_vectors() {
        let identity = TestIdentity::real_ed25519();

        let proof = TLogProof::parse(TEST_TLOG_PROOF).expect("parsing proof");

        assert_eq!(proof.index, 3);
        assert_eq!(proof.proof_hashes.len(), 2);
        assert_eq!(proof.checkpoint.origin, identity.origin);
        assert_eq!(proof.checkpoint.tree_size, 4);
        assert_eq!(proof.checkpoint.signatures.len(), 2);
        assert_eq!(proof.checkpoint.signatures[0].origin, identity.origin);
    }

    #[test]
    fn test_parse_proof_synthetic() {
        let identity = TestIdentity::fake_ed25519();
        let root_hash = Sha256::from([0xCC; 32]);
        let checkpoint = make_checkpoint(&identity, 456, &root_hash);
        let proof_str = make_tlog_proof(123, &[Sha256::from([0xAA; 32])], &checkpoint);

        let proof = TLogProof::parse(&proof_str).expect("parsing proof");

        assert_eq!(proof.index, 123);
        assert_eq!(proof.proof_hashes.len(), 1);
        assert_eq!(proof.checkpoint.origin, identity.origin);
        assert_eq!(proof.checkpoint.tree_size, 456);
        assert_eq!(proof.checkpoint.root_hash, root_hash);
        assert_eq!(proof.checkpoint.signatures.len(), 1);
    }

    #[test]
    fn test_parse_proof_invalid_header() {
        let proof_str = "invalid-header\nindex 0\n";

        let result = TLogProof::parse(proof_str);

        assert!(matches!(result, Err(TLogProofError::InvalidHeader)));
    }

    #[test]
    fn test_parse_proof_invalid_index() {
        assert!(matches!(
            TLogProof::parse("c2sp.org/tlog-proof@v1\nindex abc\n"),
            Err(TLogProofError::Format(_)) | Err(TLogProofError::InvalidIndex)
        ));
    }

    #[test]
    fn test_parse_proof_malformed_checkpoint() {
        let proof_str = "c2sp.org/tlog-proof@v1\nindex 0\n\norigin\nnot_a_number\n";
        assert!(matches!(
            TLogProof::parse(proof_str),
            Err(TLogProofError::MalformedCheckpoint(CheckpointError::Malformed))
        ));

        let proof_str2 = "c2sp.org/tlog-proof@v1\nindex 0\n\norigin\n1\nnot_b64\n";
        assert!(matches!(
            TLogProof::parse(proof_str2),
            Err(TLogProofError::MalformedCheckpoint(CheckpointError::Malformed))
        ));
    }

    #[test]
    fn test_parse_proof_with_extra_data() {
        let identity = TestIdentity::fake_ed25519();
        let entry = b"entry-data";
        let test_tree = TestTree::new(2, 0, entry);
        let checkpoint = make_checkpoint(&identity, 2, &test_tree.root());
        let proof_str = make_tlog_proof(0, &test_tree.proof(0), &checkpoint);

        // Insert an "extra" line after the header.
        let proof_with_extra = proof_str.replacen(
            "c2sp.org/tlog-proof@v1\n",
            "c2sp.org/tlog-proof@v1\nextra dGVzdA==\n",
            1,
        );

        let proof = TLogProof::parse(&proof_with_extra).unwrap();
        assert_eq!(proof.index, 0);
        let p = policy::Policy::parse(&format!("{}quorum none\n", identity.log_line())).unwrap();
        assert!(proof.verify(&p, entry).is_ok());
    }

    #[test]
    fn test_serialize_roundtrip_synthetic() {
        let identity = TestIdentity::fake_ed25519();
        let entry = b"roundtrip-entry";
        let test_tree = TestTree::new(4, 2, entry);
        let checkpoint = make_checkpoint(&identity, 4, &test_tree.root());
        let proof_str = make_tlog_proof(2, &test_tree.proof(2), &checkpoint);

        let proof = TLogProof::parse(&proof_str).unwrap();
        let displayed = proof.serialize();
        let reparsed = TLogProof::parse(&displayed).expect("re-parsing displayed proof");

        assert_eq!(reparsed, proof);
    }

    #[test]
    fn test_serialize_roundtrip_with_cosignature() {
        let log = TestIdentity::fake_ed25519();
        let witness = TestIdentity::fake_cosignature_v1();
        let entry = b"cosig-roundtrip";
        let test_tree = TestTree::new(3, 1, entry);
        let root = test_tree.root();
        let root_b64 = B64.encode(root);
        let signed_payload = format!("{}\n{}\n{}\n", log.origin, 3, root_b64);

        let log_sig = log.sign(&signed_payload, Instant::UNIX_EPOCH);
        let witness_sig = witness.sign(&signed_payload, Instant::from_unix_seconds(1700000000));

        let checkpoint = Checkpoint {
            origin: log.origin.clone(),
            tree_size: 3,
            root_hash: root,
            signed_payload,
            signatures: vec![log_sig, witness_sig],
        };

        let proof = TLogProof { index: 1, proof_hashes: test_tree.proof(1), checkpoint };
        let displayed = proof.serialize();
        let reparsed = TLogProof::parse(&displayed).expect("re-parsing displayed proof");

        assert_eq!(reparsed, proof);
    }

    #[test]
    fn test_verify_real_vectors() {
        let identity = TestIdentity::real_ed25519();
        let witness_vkey = NoteVerifyingKey::parse(TEST_WITNESS_VKEY).unwrap();
        let proof = TLogProof::parse(TEST_TLOG_PROOF).unwrap();

        let policy_str = alloc::format!(
            concat!("log {}\n", "witness w1 {}\n", "quorum w1\n"),
            identity.verifying_key.to_vkey_string(),
            witness_vkey.to_vkey_string()
        );
        let policy = policy::Policy::parse(&policy_str).unwrap();

        let result = proof.verify(&policy, TEST_ENTRY);

        assert!(result.is_ok());
    }

    #[test]
    fn test_verify_real_merkle_vectors() {
        let identity = TestIdentity::fake_ed25519();
        let proof_hashes: Vec<Sha256> = TEST_REAL_PROOF_HASHES
            .iter()
            .map(|h| Sha256::from(<[u8; 32]>::try_from(B64.decode(h).unwrap()).unwrap()))
            .collect();
        let root_hash =
            Sha256::from(<[u8; 32]>::try_from(B64.decode(TEST_REAL_ROOT_HASH).unwrap()).unwrap());
        let checkpoint = make_checkpoint(&identity, 76959, &root_hash);
        let proof_str = make_tlog_proof(76958, &proof_hashes, &checkpoint);

        let proof = TLogProof::parse(&proof_str).unwrap();

        let p = policy::Policy::parse(&format!("{}quorum none\n", identity.log_line())).unwrap();
        assert!(proof.verify(&p, TEST_REAL_ENTRY).is_ok());
    }

    #[test]
    fn test_verify_synthetic() {
        let identity = TestIdentity::fake_ed25519();
        let entry = b"valid-entry";
        let test_tree = TestTree::new(2, 0, entry);
        let checkpoint = make_checkpoint(&identity, 2, &test_tree.root());
        let proof_str = make_tlog_proof(0, &test_tree.proof(0), &checkpoint);

        let proof = TLogProof::parse(&proof_str).unwrap();

        let p = policy::Policy::parse(&format!("{}quorum none\n", identity.log_line())).unwrap();
        assert!(proof.verify(&p, entry).is_ok());
    }

    #[test]
    fn test_verify_cosignature() {
        let log = TestIdentity::fake_ed25519();
        let witness = TestIdentity::fake_cosignature_v1();
        let entry = b"valid-entry";
        let test_tree = TestTree::new(3, 1, entry);
        let root = test_tree.root();
        let root_b64 = B64.encode(root);
        let signed_payload = format!("{}\n{}\n{}\n", log.origin, 3, root_b64);

        // Log signs with Ed25519 (type 0x01).
        let log_sig = log.sign(&signed_payload, Instant::UNIX_EPOCH);
        // Witness cosigns with timestamp (type 0x04).
        let witness_sig = witness.sign(&signed_payload, Instant::from_unix_seconds(1700000000));

        let checkpoint = Checkpoint {
            origin: log.origin.clone(),
            tree_size: 3,
            root_hash: root,
            signed_payload,
            signatures: vec![log_sig, witness_sig],
        };

        let proof_str = make_tlog_proof(1, &test_tree.proof(1), &checkpoint);
        let proof = TLogProof::parse(&proof_str).unwrap();

        let policy_str = alloc::format!(
            concat!("log {}\n", "witness w1 {}\n", "quorum w1\n"),
            log.verifying_key.to_vkey_string(),
            witness.verifying_key.to_vkey_string()
        );
        let policy = policy::Policy::parse(&policy_str).unwrap();

        assert!(proof.verify(&policy, entry).is_ok());
    }

    #[test]
    fn test_verify_with_extension_lines() {
        let identity = TestIdentity::fake_ed25519();
        let entry = b"ext-entry";
        let test_tree = TestTree::new(2, 0, entry);
        let root = test_tree.root();
        let root_b64 = B64.encode(root);

        // Build signed_payload with an extension line.
        let signed_payload = format!("{}\n{}\n{}\nextra-data\n", identity.origin, 2, root_b64);
        let sig = identity.sign(&signed_payload, Instant::UNIX_EPOCH);

        let checkpoint = Checkpoint {
            origin: identity.origin.clone(),
            tree_size: 2,
            root_hash: root,
            signed_payload,
            signatures: vec![sig],
        };

        let proof_str = make_tlog_proof(0, &test_tree.proof(0), &checkpoint);
        let proof = TLogProof::parse(&proof_str).unwrap();

        assert_eq!(proof.checkpoint.signed_payload, checkpoint.signed_payload);
        let p = policy::Policy::parse(&format!("{}quorum none\n", identity.log_line())).unwrap();
        assert!(proof.verify(&p, entry).is_ok());
    }

    #[test]
    fn test_verify_single_leaf_tree() {
        let identity = TestIdentity::fake_ed25519();
        let entry = b"single-leaf";
        let test_tree = TestTree::new(1, 0, entry);
        let checkpoint = make_checkpoint(&identity, 1, &test_tree.root());
        let proof_str = make_tlog_proof(0, &test_tree.proof(0), &checkpoint);

        let proof = TLogProof::parse(&proof_str).unwrap();

        let p = policy::Policy::parse(&format!("{}quorum none\n", identity.log_line())).unwrap();
        assert!(proof.verify(&p, entry).is_ok());
    }

    #[test]
    fn test_verify_last_leaf() {
        let identity = TestIdentity::fake_ed25519();
        let entry = b"last-leaf";
        let tree_size = 16;
        let last_index = tree_size - 1;
        let test_tree = TestTree::new(tree_size, last_index, entry);
        let checkpoint = make_checkpoint(&identity, tree_size as u64, &test_tree.root());
        let proof_str =
            make_tlog_proof(last_index as u64, &test_tree.proof(last_index), &checkpoint);

        let proof = TLogProof::parse(&proof_str).unwrap();

        let p = policy::Policy::parse(&format!("{}quorum none\n", identity.log_line())).unwrap();
        assert!(proof.verify(&p, entry).is_ok());
    }

    #[test]
    fn test_verify_wrong_origin() {
        let identity = TestIdentity::fake_ed25519();
        let other = TestIdentity::ed25519("wrong.com/log", [99u8; 32]);
        let entry = b"data";
        let test_tree = TestTree::new(2, 0, entry);
        let checkpoint = make_checkpoint(&identity, 2, &test_tree.root());
        let proof_str = make_tlog_proof(0, &test_tree.proof(0), &checkpoint);
        let proof = TLogProof::parse(&proof_str).unwrap();

        // Policy with a different origin — no log key matches.
        let p = policy::Policy::parse(&format!("{}quorum none\n", other.log_line())).unwrap();
        let result = proof.verify(&p, entry);

        assert!(matches!(result, Err(TLogProofError::SignatureMismatch)));
    }

    #[test]
    fn test_verify_wrong_entry() {
        let identity = TestIdentity::fake_ed25519();
        let entry = b"real-entry";
        let test_tree = TestTree::new(2, 0, entry);
        let checkpoint = make_checkpoint(&identity, 2, &test_tree.root());
        let proof_str = make_tlog_proof(0, &test_tree.proof(0), &checkpoint);
        let proof = TLogProof::parse(&proof_str).unwrap();

        let p = policy::Policy::parse(&format!("{}quorum none\n", identity.log_line())).unwrap();
        let result = proof.verify(&p, b"fake-entry");

        assert!(matches!(result, Err(TLogProofError::RootMismatch)));
    }

    #[test]
    fn test_verify_tampered_signature() {
        let identity = TestIdentity::fake_ed25519();
        let entry = b"data";
        let test_tree = TestTree::new(2, 0, entry);
        let checkpoint = make_checkpoint(&identity, 2, &test_tree.root());
        let mut proof_str = make_tlog_proof(0, &test_tree.proof(0), &checkpoint);

        // Replace the signature with garbage bytes.
        let parts: Vec<&str> = proof_str.split("— ").collect();
        let mut bad_sig_bytes = vec![];
        bad_sig_bytes.extend_from_slice(&identity.verifying_key.key_id_hint);
        bad_sig_bytes.extend_from_slice(&[0xBB; 64]);
        let bad_sig = B64.encode(bad_sig_bytes);
        proof_str = format!("{}— {} {}", parts[0], identity.origin, bad_sig);

        let proof = TLogProof::parse(&proof_str).unwrap();

        let p = policy::Policy::parse(&format!("{}quorum none\n", identity.log_line())).unwrap();
        let result = proof.verify(&p, entry);

        assert!(matches!(
            result,
            Err(TLogProofError::Note(NoteError::SignatureVerificationFailed))
        ));
    }

    #[test]
    fn test_verify_signature_mismatch() {
        let identity = TestIdentity::fake_ed25519();
        let entry = b"valid-entry";
        let test_tree = TestTree::new(2, 0, entry);
        let checkpoint = make_checkpoint(&identity, 2, &test_tree.root());
        let proof_str = make_tlog_proof(0, &test_tree.proof(0), &checkpoint);
        let proof = TLogProof::parse(&proof_str).unwrap();

        let other = TestIdentity::ed25519(FAKE_ORIGIN, [99u8; 32]);

        // Policy with a key whose key_id_hint won't match any signature.
        let p = policy::Policy::parse(&format!("{}quorum none\n", other.log_line())).unwrap();
        assert!(matches!(proof.verify(&p, entry), Err(TLogProofError::SignatureMismatch)));
    }

    #[test]
    fn test_verify_invalid_merkle_chain() {
        let identity = TestIdentity::fake_ed25519();
        let entry = b"valid-entry";
        let test_tree = TestTree::new(5, 0, entry);
        let checkpoint = make_checkpoint(&identity, 5, &test_tree.root());
        // Use index 5 which is >= tree_size 5, making the chain invalid.
        let proof_str = make_tlog_proof(5, &test_tree.proof(0), &checkpoint);

        let proof = TLogProof::parse(&proof_str).unwrap();

        let p = policy::Policy::parse(&format!("{}quorum none\n", identity.log_line())).unwrap();
        assert!(matches!(proof.verify(&p, entry), Err(TLogProofError::InvalidMerkleChain)));
    }

    #[test]
    fn test_verify_with_policy_success() {
        let log = TestIdentity::fake_ed25519();
        let witness1 = TestIdentity::fake_cosignature_v1();
        let witness2 = TestIdentity::cosignature_v1("fake-witness-2", [44u8; 32]);
        let entry = b"valid-entry";
        let test_tree = TestTree::new(3, 1, entry);
        let root = test_tree.root();
        let root_b64 = B64.encode(root);
        let signed_payload = format!("{}\n{}\n{}\n", log.origin, 3, root_b64);

        let log_sig = log.sign(&signed_payload, Instant::UNIX_EPOCH);
        let witness1_sig = witness1.sign(&signed_payload, Instant::from_unix_seconds(1700000000));
        let witness2_sig = witness2.sign(&signed_payload, Instant::from_unix_seconds(1700000001));

        let checkpoint = Checkpoint {
            origin: log.origin.clone(),
            tree_size: 3,
            root_hash: root,
            signed_payload,
            signatures: vec![log_sig, witness1_sig, witness2_sig],
        };

        let proof_str = make_tlog_proof(1, &test_tree.proof(1), &checkpoint);
        let proof = TLogProof::parse(&proof_str).unwrap();

        // Policy requiring any 1 of the 2 witnesses
        let policy_str = format!(
            concat!(
                "log {}\n",
                "witness w1 {}\n",
                "witness w2 {}\n",
                "group g any w1 w2\n",
                "quorum g\n",
            ),
            log.verifying_key.to_vkey_string(),
            witness1.verifying_key.to_vkey_string(),
            witness2.verifying_key.to_vkey_string()
        );
        let policy = policy::Policy::parse(&policy_str).unwrap();

        assert!(proof.verify(&policy, entry).is_ok());
    }

    #[test]
    fn test_verify_with_policy_any_single_signer() {
        let log = TestIdentity::fake_ed25519();
        let witness1 = TestIdentity::fake_cosignature_v1();
        let witness2 = TestIdentity::cosignature_v1("fake-witness-2", [44u8; 32]);
        let entry = b"valid-entry";
        let test_tree = TestTree::new(3, 1, entry);
        let root = test_tree.root();
        let root_b64 = B64.encode(root);
        let signed_payload = format!("{}\n{}\n{}\n", log.origin, 3, root_b64);

        let log_sig = log.sign(&signed_payload, Instant::UNIX_EPOCH);
        // Only witness1 cosigns.
        let witness1_sig = witness1.sign(&signed_payload, Instant::from_unix_seconds(1700000000));

        let checkpoint = Checkpoint {
            origin: log.origin.clone(),
            tree_size: 3,
            root_hash: root,
            signed_payload,
            signatures: vec![log_sig, witness1_sig],
        };

        let proof_str = make_tlog_proof(1, &test_tree.proof(1), &checkpoint);
        let proof = TLogProof::parse(&proof_str).unwrap();

        // Policy requiring any 1 of the 2 witnesses. witness1 signed, so this
        // should succeed even though witness2 did not.
        let policy_str = format!(
            concat!(
                "log {}\n",
                "witness w1 {}\n",
                "witness w2 {}\n",
                "group g any w1 w2\n",
                "quorum g\n",
            ),
            log.verifying_key.to_vkey_string(),
            witness1.verifying_key.to_vkey_string(),
            witness2.verifying_key.to_vkey_string()
        );
        let policy = policy::Policy::parse(&policy_str).unwrap();

        assert!(proof.verify(&policy, entry).is_ok());
    }

    #[test]
    fn test_verify_with_policy_failure() {
        let log = TestIdentity::fake_ed25519();
        let witness1 = TestIdentity::fake_cosignature_v1();
        let witness2 = TestIdentity::cosignature_v1("fake-witness-2", [44u8; 32]);
        let entry = b"valid-entry";
        let test_tree = TestTree::new(3, 1, entry);
        let root = test_tree.root();
        let root_b64 = B64.encode(root);
        let signed_payload = format!("{}\n{}\n{}\n", log.origin, 3, root_b64);

        let log_sig = log.sign(&signed_payload, Instant::UNIX_EPOCH);
        let witness1_sig = witness1.sign(&signed_payload, Instant::from_unix_seconds(1700000000));

        let checkpoint = Checkpoint {
            origin: log.origin.clone(),
            tree_size: 3,
            root_hash: root,
            signed_payload,
            signatures: vec![log_sig, witness1_sig], // Missing witness2 sig
        };

        let proof_str = make_tlog_proof(1, &test_tree.proof(1), &checkpoint);
        let proof = TLogProof::parse(&proof_str).unwrap();

        // Policy requiring ALL 2 witnesses
        let policy_str = format!(
            concat!(
                "log {}\n",
                "witness w1 {}\n",
                "witness w2 {}\n",
                "group g all w1 w2\n",
                "quorum g\n",
            ),
            log.verifying_key.to_vkey_string(),
            witness1.verifying_key.to_vkey_string(),
            witness2.verifying_key.to_vkey_string()
        );
        let policy = policy::Policy::parse(&policy_str).unwrap();

        let result = proof.verify(&policy, entry);

        assert!(matches!(result, Err(TLogProofError::InsufficientWitnesses)));
    }

    #[test]
    fn test_verify_ml_dsa_log_origin() {
        let log = TestIdentity::subtree_v1(FAKE_ORIGIN);
        let entry = b"ml-dsa-log-entry";
        let test_tree = TestTree::new(4, 2, entry);
        let checkpoint = make_checkpoint(&log, 4, &test_tree.root());
        let proof_str = make_tlog_proof(2, &test_tree.proof(2), &checkpoint);

        let proof = TLogProof::parse(&proof_str).unwrap();

        let p = policy::Policy::parse(&format!("{}quorum none\n", log.log_line())).unwrap();
        assert!(proof.verify(&p, entry).is_ok());
    }

    #[test]
    fn test_verify_ml_dsa_log_origin_wrong_entry() {
        let log = TestIdentity::subtree_v1(FAKE_ORIGIN);
        let entry = b"ml-dsa-real-entry";
        let test_tree = TestTree::new(2, 0, entry);
        let checkpoint = make_checkpoint(&log, 2, &test_tree.root());
        let proof_str = make_tlog_proof(0, &test_tree.proof(0), &checkpoint);

        let proof = TLogProof::parse(&proof_str).unwrap();

        let p = policy::Policy::parse(&format!("{}quorum none\n", log.log_line())).unwrap();
        assert!(matches!(proof.verify(&p, b"wrong-entry"), Err(TLogProofError::RootMismatch)));
    }

    #[test]
    fn test_serialize_roundtrip_ml_dsa_log() {
        let log = TestIdentity::subtree_v1(FAKE_ORIGIN);
        let entry = b"ml-dsa-roundtrip";
        let test_tree = TestTree::new(4, 1, entry);
        let checkpoint = make_checkpoint(&log, 4, &test_tree.root());
        let proof_str = make_tlog_proof(1, &test_tree.proof(1), &checkpoint);

        let proof = TLogProof::parse(&proof_str).unwrap();
        let displayed = proof.serialize();
        let reparsed = TLogProof::parse(&displayed).unwrap();

        assert_eq!(reparsed, proof);
    }

    #[test]
    fn test_verify_ml_dsa_witness_cosignature() {
        let log = TestIdentity::fake_ed25519();
        let witness = TestIdentity::fake_subtree_v1();
        let entry = b"ml-dsa-witness-entry";
        let test_tree = TestTree::new(3, 1, entry);
        let root = test_tree.root();
        let root_b64 = B64.encode(root);
        let signed_payload = format!("{}\n{}\n{}\n", log.origin, 3, root_b64);

        let log_sig = log.sign(&signed_payload, Instant::UNIX_EPOCH);
        let witness_sig = witness.sign(&signed_payload, Instant::from_unix_seconds(1700000000));

        let checkpoint = Checkpoint {
            origin: log.origin.clone(),
            tree_size: 3,
            root_hash: root,
            signed_payload,
            signatures: vec![log_sig, witness_sig],
        };

        let proof_str = make_tlog_proof(1, &test_tree.proof(1), &checkpoint);
        let proof = TLogProof::parse(&proof_str).unwrap();

        let policy_str = alloc::format!(
            concat!("log {}\n", "witness w1 {}\n", "quorum w1\n"),
            log.verifying_key.to_vkey_string(),
            witness.verifying_key.to_vkey_string()
        );
        let policy = policy::Policy::parse(&policy_str).unwrap();

        assert!(proof.verify(&policy, entry).is_ok());
    }

    #[test]
    fn test_serialize_roundtrip_ml_dsa_witness() {
        let log = TestIdentity::fake_ed25519();
        let witness = TestIdentity::fake_subtree_v1();
        let entry = b"ml-dsa-cosig-roundtrip";
        let test_tree = TestTree::new(3, 1, entry);
        let root = test_tree.root();
        let root_b64 = B64.encode(root);
        let signed_payload = format!("{}\n{}\n{}\n", log.origin, 3, root_b64);

        let log_sig = log.sign(&signed_payload, Instant::UNIX_EPOCH);
        let witness_sig = witness.sign(&signed_payload, Instant::from_unix_seconds(1700000000));

        let checkpoint = Checkpoint {
            origin: log.origin.clone(),
            tree_size: 3,
            root_hash: root,
            signed_payload,
            signatures: vec![log_sig, witness_sig],
        };

        let proof = TLogProof { index: 1, proof_hashes: test_tree.proof(1), checkpoint };
        let displayed = proof.serialize();
        let reparsed = TLogProof::parse(&displayed).unwrap();

        assert_eq!(reparsed, proof);
    }

    #[test]
    fn test_verify_ml_dsa_log_with_ed25519_witness() {
        let log = TestIdentity::subtree_v1(FAKE_ORIGIN);
        let witness = TestIdentity::fake_cosignature_v1();
        let entry = b"mixed-keys-entry";
        let test_tree = TestTree::new(4, 2, entry);
        let root = test_tree.root();
        let root_b64 = B64.encode(root);
        let signed_payload = format!("{}\n{}\n{}\n", log.origin, 4, root_b64);

        let log_sig = log.sign(&signed_payload, Instant::UNIX_EPOCH);
        let witness_sig = witness.sign(&signed_payload, Instant::from_unix_seconds(1700000000));

        let checkpoint = Checkpoint {
            origin: log.origin.clone(),
            tree_size: 4,
            root_hash: root,
            signed_payload,
            signatures: vec![log_sig, witness_sig],
        };

        let proof_str = make_tlog_proof(2, &test_tree.proof(2), &checkpoint);
        let proof = TLogProof::parse(&proof_str).unwrap();

        let policy_str = alloc::format!(
            concat!("log {}\n", "witness w1 {}\n", "quorum w1\n"),
            log.verifying_key.to_vkey_string(),
            witness.verifying_key.to_vkey_string()
        );
        let policy = policy::Policy::parse(&policy_str).unwrap();

        assert!(proof.verify(&policy, entry).is_ok());
    }

    #[test]
    fn test_verify_ed25519_log_with_ml_dsa_witness() {
        let log = TestIdentity::fake_ed25519();
        let witness = TestIdentity::fake_subtree_v1();
        let entry = b"ed25519-log-ml-dsa-witness";
        let test_tree = TestTree::new(4, 3, entry);
        let root = test_tree.root();
        let root_b64 = B64.encode(root);
        let signed_payload = format!("{}\n{}\n{}\n", log.origin, 4, root_b64);

        let log_sig = log.sign(&signed_payload, Instant::UNIX_EPOCH);
        let witness_sig = witness.sign(&signed_payload, Instant::from_unix_seconds(1700000002));

        let checkpoint = Checkpoint {
            origin: log.origin.clone(),
            tree_size: 4,
            root_hash: root,
            signed_payload,
            signatures: vec![log_sig, witness_sig],
        };

        let proof_str = make_tlog_proof(3, &test_tree.proof(3), &checkpoint);
        let proof = TLogProof::parse(&proof_str).unwrap();

        let policy_str = alloc::format!(
            concat!("log {}\n", "witness w1 {}\n", "quorum w1\n"),
            log.verifying_key.to_vkey_string(),
            witness.verifying_key.to_vkey_string()
        );
        let policy = policy::Policy::parse(&policy_str).unwrap();

        assert!(proof.verify(&policy, entry).is_ok());
    }

    #[test]
    fn test_verify_ml_dsa_log_with_ml_dsa_witness() {
        let log = TestIdentity::subtree_v1(FAKE_ORIGIN);
        let witness = TestIdentity::fake_subtree_v1();
        let entry = b"all-ml-dsa-entry";
        let test_tree = TestTree::new(2, 0, entry);
        let root = test_tree.root();
        let root_b64 = B64.encode(root);
        let signed_payload = format!("{}\n{}\n{}\n", log.origin, 2, root_b64);

        let log_sig = log.sign(&signed_payload, Instant::UNIX_EPOCH);
        let witness_sig = witness.sign(&signed_payload, Instant::from_unix_seconds(1700000000));

        let checkpoint = Checkpoint {
            origin: log.origin.clone(),
            tree_size: 2,
            root_hash: root,
            signed_payload,
            signatures: vec![log_sig, witness_sig],
        };

        let proof_str = make_tlog_proof(0, &test_tree.proof(0), &checkpoint);
        let proof = TLogProof::parse(&proof_str).unwrap();

        let policy_str = alloc::format!(
            concat!("log {}\n", "witness w1 {}\n", "quorum w1\n"),
            log.verifying_key.to_vkey_string(),
            witness.verifying_key.to_vkey_string()
        );
        let policy = policy::Policy::parse(&policy_str).unwrap();

        assert!(proof.verify(&policy, entry).is_ok());
    }

    #[test]
    fn test_verify_policy_mixed_witnesses() {
        let log = TestIdentity::fake_ed25519();
        let ed_witness = TestIdentity::fake_cosignature_v1();
        let ml_witness = TestIdentity::fake_subtree_v1();
        let entry = b"mixed-witness-entry";
        let test_tree = TestTree::new(4, 2, entry);
        let root = test_tree.root();
        let root_b64 = B64.encode(root);
        let signed_payload = format!("{}\n{}\n{}\n", log.origin, 4, root_b64);

        let log_sig = log.sign(&signed_payload, Instant::UNIX_EPOCH);
        let ed_sig = ed_witness.sign(&signed_payload, Instant::from_unix_seconds(1700000000));
        let ml_sig = ml_witness.sign(&signed_payload, Instant::from_unix_seconds(1700000001));

        let checkpoint = Checkpoint {
            origin: log.origin.clone(),
            tree_size: 4,
            root_hash: root,
            signed_payload,
            signatures: vec![log_sig, ed_sig, ml_sig],
        };

        let proof_str = make_tlog_proof(2, &test_tree.proof(2), &checkpoint);
        let proof = TLogProof::parse(&proof_str).unwrap();

        // Policy requiring all witnesses (one Ed25519, one ML-DSA).
        let policy_str = format!(
            concat!(
                "log {}\n",
                "witness w1 {}\n",
                "witness w2 {}\n",
                "group g all w1 w2\n",
                "quorum g\n",
            ),
            log.verifying_key.to_vkey_string(),
            ed_witness.verifying_key.to_vkey_string(),
            ml_witness.verifying_key.to_vkey_string()
        );
        let policy = policy::Policy::parse(&policy_str).unwrap();

        assert!(proof.verify(&policy, entry).is_ok());
    }

    #[test]
    fn test_verify_policy_mixed_witnesses_missing_ml_dsa() {
        let log = TestIdentity::fake_ed25519();
        let ed_witness = TestIdentity::fake_cosignature_v1();
        let ml_witness = TestIdentity::fake_subtree_v1();
        let entry = b"mixed-witness-missing";
        let test_tree = TestTree::new(4, 2, entry);
        let root = test_tree.root();
        let root_b64 = B64.encode(root);
        let signed_payload = format!("{}\n{}\n{}\n", log.origin, 4, root_b64);

        let log_sig = log.sign(&signed_payload, Instant::UNIX_EPOCH);
        // Only the Ed25519 witness cosigns; ML-DSA witness is absent.
        let ed_sig = ed_witness.sign(&signed_payload, Instant::from_unix_seconds(1700000000));

        let checkpoint = Checkpoint {
            origin: log.origin.clone(),
            tree_size: 4,
            root_hash: root,
            signed_payload,
            signatures: vec![log_sig, ed_sig],
        };

        let proof_str = make_tlog_proof(2, &test_tree.proof(2), &checkpoint);
        let proof = TLogProof::parse(&proof_str).unwrap();

        // Policy requiring ALL witnesses — should fail.
        let policy_str = format!(
            concat!(
                "log {}\n",
                "witness w1 {}\n",
                "witness w2 {}\n",
                "group g all w1 w2\n",
                "quorum g\n",
            ),
            log.verifying_key.to_vkey_string(),
            ed_witness.verifying_key.to_vkey_string(),
            ml_witness.verifying_key.to_vkey_string()
        );
        let policy = policy::Policy::parse(&policy_str).unwrap();

        assert!(matches!(proof.verify(&policy, entry), Err(TLogProofError::InsufficientWitnesses)));
    }
}
