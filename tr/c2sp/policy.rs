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

//! [C2SP tlog-policy](https://c2sp.org/tlog-policy) parser and evaluator.
//!
//! A [`Policy`] defines the trusted log keys and the witness quorum required
//! for a checkpoint to be considered valid.
//!
//! Policies are parsed from the
//! [C2SP tlog-policy format](https://c2sp.org/tlog-policy),
//! with the additional requirement that public keys must be provided as
//! [C2SP verifying key strings](https://c2sp.org/signed-note#verifier-keys)
//! (vkey format) rather than raw hex.
//!
//! # Example
//!
//! ```text
//! log example.com/log+deadbeef+AeebEb...
//! witness wit-1 witness.example.com/w1+4b7fca75+AStu...
//! witness wit-2 witness.example.com/w2+abcd1234+BKxz...
//! group mygroup 1 wit-1 wit-2
//! quorum mygroup
//! ```

use alloc::{collections::BTreeMap, string::String, vec::Vec};
use core::fmt;

use oak_proto_rust::oak::attestation::v1::C2sptLogProofReferenceValue;
use thiserror::Error;

use crate::note::{NoteVerifyingKey, VerifyingKey};

/// A policy-local name identifying a witness or group within a
/// [`Policy`].
///
/// These names are used to cross-reference entries in the policy file (e.g. a
/// group's member list refers to witness or group names defined earlier).
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct QuorumName(String);

impl QuorumName {
    fn new(name: &str) -> Self {
        Self(name.into())
    }
}

impl fmt::Display for QuorumName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// Error type for policy parsing.
#[derive(Debug, Error)]
pub enum PolicyError {
    #[error("line {line}: {reason}")]
    Parse { line: usize, reason: String },
}

/// A [C2SP tlog-policy](https://c2sp.org/tlog-policy) specifying trusted log
/// keys and witness quorum.
///
/// The policy specifies a set of trusted log verifying keys, a set of known
/// witnesses, and the quorum rule that determines whether enough witness
/// cosignatures are present for a checkpoint to be considered valid.
///
/// Log public keys must be
/// [C2SP verifying key strings](https://c2sp.org/signed-note#verifier-keys)
/// with variant [`VerifyingKey::Ed25519`] (type 0x01) or
/// [`VerifyingKey::MlDsa44SubtreeV1`] (type 0x06).
///
/// Witness public keys must be
/// [C2SP verifying key strings](https://c2sp.org/signed-note#verifier-keys)
/// with variant [`VerifyingKey::Ed25519CosignatureV1`] (type 0x04) or
/// [`VerifyingKey::MlDsa44SubtreeV1`] (type 0x06).
#[derive(Debug)]
pub struct Policy {
    /// Trusted log verifying keys. Multiple keys are allowed to support key
    /// rotation; during verification exactly one (whose origin matches the
    /// checkpoint's origin) must produce a valid signature.
    log_keys: Vec<NoteVerifyingKey>,
    /// Named quorum entries (witnesses and groups), indexed by policy-local
    /// name.
    quorums: BTreeMap<QuorumName, Quorum>,
    /// The root quorum name. `None` means `quorum none` — no witnesses
    /// required.
    quorum: Option<QuorumName>,
}

/// Internal representation of a quorum tree node.
#[derive(Debug)]
#[allow(clippy::large_enum_variant)]
enum Quorum {
    /// A single witness, identified by its C2SP verifying key.
    Witness(NoteVerifyingKey),
    /// A threshold group: at least `k` of `members` must be satisfied.
    Group { k: usize, members: Vec<QuorumName> },
}

impl Policy {
    /// Parses a policy from its text representation.
    ///
    /// Follows the
    /// [C2SP tlog-policy format](https://c2sp.org/tlog-policy),
    /// with the requirement that all public keys are specified as
    /// [C2SP verifying key strings](https://c2sp.org/signed-note#verifier-keys).
    ///
    /// The policy must contain exactly one `quorum` line. The set of
    /// logs may be empty if the application knows the appropriate log(s)
    /// from other context.
    pub fn parse(data: &str) -> Result<Self, PolicyError> {
        let mut log_keys = Vec::new();
        let mut quorums = BTreeMap::new();
        let mut quorum_set = false;
        let mut root_quorum: Option<QuorumName> = None;

        for (lineno, line) in data.lines().enumerate() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }

            let tokens: Vec<&str> = line.split_ascii_whitespace().collect();
            match tokens[0] {
                "log" => {
                    let nargs = tokens.len() - 1;
                    if !(1..=2).contains(&nargs) {
                        return Err(PolicyError::Parse {
                            line: lineno + 1,
                            reason: alloc::format!(
                                "invalid log rule: expected 1 or 2 arguments, got {nargs}"
                            ),
                        });
                    }
                    // The vkey is the first argument; the optional second
                    // argument is a URL (ignored).
                    // See: https://c2sp.org/tlog-policy#defining-a-log
                    let vkey_str = tokens[1];

                    let vkey =
                        NoteVerifyingKey::parse(vkey_str).map_err(|_| PolicyError::Parse {
                            line: lineno + 1,
                            reason: "log key must be a C2SP verifying key string".into(),
                        })?;

                    // Validate: log keys must be Ed25519 (0x01) or
                    // ML-DSA-44 (0x06).
                    #[cfg(feature = "ml_dsa")]
                    let ml_dsa_ok = matches!(vkey.verifying_key, VerifyingKey::MlDsa44SubtreeV1(_));
                    #[cfg(not(feature = "ml_dsa"))]
                    let ml_dsa_ok = false;
                    if !matches!(vkey.verifying_key, VerifyingKey::Ed25519(_)) && !ml_dsa_ok {
                        return Err(PolicyError::Parse {
                            line: lineno + 1,
                            reason: "log key must have Ed25519 (0x01) or ML-DSA-44 (0x06) type"
                                .into(),
                        });
                    }

                    // Reject duplicate log keys (same underlying public
                    // key).
                    if log_keys.iter().any(|existing: &NoteVerifyingKey| {
                        existing.verifying_key == vkey.verifying_key
                    }) {
                        return Err(PolicyError::Parse {
                            line: lineno + 1,
                            reason: "duplicate log key".into(),
                        });
                    }

                    log_keys.push(vkey);
                }
                "witness" => {
                    let nargs = tokens.len() - 1;
                    if !(2..=3).contains(&nargs) {
                        return Err(PolicyError::Parse {
                            line: lineno + 1,
                            reason: alloc::format!(
                                "invalid witness rule: expected 2 or 3 arguments, got {nargs}"
                            ),
                        });
                    }
                    let name = tokens[1];
                    if name == "none" {
                        return Err(PolicyError::Parse {
                            line: lineno + 1,
                            reason: "`none` is a reserved name".into(),
                        });
                    }
                    let vkey_str = tokens[2];

                    // Parse the vkey as a C2SP verifying key.
                    let vkey =
                        NoteVerifyingKey::parse(vkey_str).map_err(|_| PolicyError::Parse {
                            line: lineno + 1,
                            reason: "witness key must be a C2SP verifying key string".into(),
                        })?;

                    // Validate: witness keys must be a cosignature type
                    // (0x04 or 0x06).
                    #[cfg(feature = "ml_dsa")]
                    let ml_dsa_ok = matches!(vkey.verifying_key, VerifyingKey::MlDsa44SubtreeV1(_));
                    #[cfg(not(feature = "ml_dsa"))]
                    let ml_dsa_ok = false;
                    if !matches!(vkey.verifying_key, VerifyingKey::Ed25519CosignatureV1(_))
                        && !ml_dsa_ok
                    {
                        return Err(PolicyError::Parse {
                            line: lineno + 1,
                            reason: "witness key must have a cosignature type (0x04 or 0x06)"
                                .into(),
                        });
                    }

                    let name = QuorumName::new(name);
                    if quorums.contains_key(&name) {
                        return Err(PolicyError::Parse {
                            line: lineno + 1,
                            reason: alloc::format!("duplicate name `{name}`"),
                        });
                    }

                    // Reject duplicate witness keys (same underlying
                    // public key).
                    for existing in quorums.values() {
                        if let Quorum::Witness(existing_vkey) = existing
                            && existing_vkey.verifying_key == vkey.verifying_key
                        {
                            return Err(PolicyError::Parse {
                                line: lineno + 1,
                                reason: "duplicate witness key".into(),
                            });
                        }
                    }

                    quorums.insert(name, Quorum::Witness(vkey));
                }
                "group" => {
                    let nargs = tokens.len() - 1;
                    if nargs < 3 {
                        return Err(PolicyError::Parse {
                            line: lineno + 1,
                            reason: alloc::format!(
                                "invalid group rule: expected at least 3 arguments, got {nargs}"
                            ),
                        });
                    }
                    let name = tokens[1];
                    if name == "none" {
                        return Err(PolicyError::Parse {
                            line: lineno + 1,
                            reason: "`none` is a reserved name".into(),
                        });
                    }
                    let k_str = tokens[2];
                    let members: Vec<QuorumName> =
                        tokens[3..].iter().map(|s| QuorumName::new(s)).collect();

                    let k = parse_threshold(k_str, members.len())
                        .map_err(|reason| PolicyError::Parse { line: lineno + 1, reason })?;

                    let name = QuorumName::new(name);
                    if quorums.contains_key(&name) {
                        return Err(PolicyError::Parse {
                            line: lineno + 1,
                            reason: alloc::format!("duplicate name `{name}`"),
                        });
                    }

                    // Validate all members are unique and refer to
                    // previously defined names.
                    let mut seen_members = alloc::collections::BTreeSet::new();
                    for member in &members {
                        if !seen_members.insert(member) {
                            return Err(PolicyError::Parse {
                                line: lineno + 1,
                                reason: alloc::format!("duplicate group member `{member}`"),
                            });
                        }
                        if !quorums.contains_key(member) {
                            return Err(PolicyError::Parse {
                                line: lineno + 1,
                                reason: alloc::format!("unknown group member `{member}`"),
                            });
                        }
                    }

                    quorums.insert(name, Quorum::Group { k, members });
                }
                "quorum" => {
                    if tokens.len() != 2 {
                        return Err(PolicyError::Parse {
                            line: lineno + 1,
                            reason: "invalid quorum rule: expected exactly one argument".into(),
                        });
                    }
                    if quorum_set {
                        return Err(PolicyError::Parse {
                            line: lineno + 1,
                            reason: "quorum already set".into(),
                        });
                    }
                    quorum_set = true;

                    let name = tokens[1];
                    if name != "none" {
                        let name = QuorumName::new(name);
                        if !quorums.contains_key(&name) {
                            return Err(PolicyError::Parse {
                                line: lineno + 1,
                                reason: alloc::format!("unknown quorum name `{name}`"),
                            });
                        }
                        root_quorum = Some(name);
                    }
                }
                unknown => {
                    return Err(PolicyError::Parse {
                        line: lineno + 1,
                        reason: alloc::format!("unknown keyword `{unknown}`"),
                    });
                }
            }
        }

        if !quorum_set {
            return Err(PolicyError::Parse {
                line: data.lines().count(),
                reason: "no quorum line found".into(),
            });
        }

        Ok(Policy { log_keys, quorums, quorum: root_quorum })
    }

    /// Returns the trusted log verifying keys specified in the policy.
    ///
    /// Multiple keys may be present to support key rotation. During
    /// verification exactly one must produce a valid signature.
    pub fn log_keys(&self) -> &[NoteVerifyingKey] {
        &self.log_keys
    }

    /// Returns an iterator over all witness verifying keys defined in the
    /// policy.
    pub fn witness_keys(&self) -> impl Iterator<Item = &NoteVerifyingKey> {
        self.quorums
            .values()
            .filter_map(|q| if let Quorum::Witness(vkey) = q { Some(vkey) } else { None })
    }

    /// Checks whether the given set of verified witness keys satisfies the
    /// policy's quorum requirements.
    ///
    /// `verified_keys` should contain only the [`NoteVerifyingKey`]s whose
    /// cosignatures have been cryptographically verified. This function does
    /// **not** verify any signatures itself — it only evaluates the quorum
    /// tree.
    ///
    /// Returns `true` if the quorum is satisfied, or if the policy specifies
    /// `quorum none`.
    pub fn check_quorum(&self, verified_keys: &[&NoteVerifyingKey]) -> bool {
        match &self.quorum {
            None => true,
            Some(name) => {
                let root = self.quorums.get(name).expect("quorum must be in quorums");
                self.satisfies(verified_keys, root)
            }
        }
    }

    /// Recursively evaluates whether the given verified keys satisfy a quorum
    /// node.
    fn satisfies(&self, verified_keys: &[&NoteVerifyingKey], quorum: &Quorum) -> bool {
        match quorum {
            Quorum::Witness(witness_key) => verified_keys.contains(&witness_key),
            Quorum::Group { k, members } => {
                members
                    .iter()
                    .filter(|m| {
                        let member = self.quorums.get(m).expect("group members must be in quorums");
                        self.satisfies(verified_keys, member)
                    })
                    .count()
                    >= *k
            }
        }
    }
}

impl TryFrom<&C2sptLogProofReferenceValue> for Policy {
    type Error = PolicyError;

    fn try_from(ref_value: &C2sptLogProofReferenceValue) -> Result<Self, Self::Error> {
        Self::parse(&ref_value.policy)
    }
}

/// Parses a threshold value: `"any"` → 1, `"all"` → n, or a decimal
/// integer k where 1 ≤ k ≤ n.
fn parse_threshold(s: &str, n: usize) -> Result<usize, String> {
    match s {
        "any" => Ok(1),
        "all" => Ok(n),
        _ => {
            let k: usize = s.parse().map_err(|_| alloc::format!("invalid threshold `{s}`"))?;
            if (1..=n).contains(&k) {
                Ok(k)
            } else {
                Err(alloc::format!(
                    "threshold {k} out of range for group of size {n}, must satisfy 1 <= k <= {n}"
                ))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use ed25519_dalek::SigningKey;

    use super::*;
    use crate::alloc::string::ToString;

    /// Helper to create a NoteVerifyingKey for testing. Derives a valid
    /// Ed25519 public key from the given raw secret key bytes.
    fn make_witness_vkey(origin: &str, raw: [u8; 32]) -> NoteVerifyingKey {
        let vk = SigningKey::from_bytes(&raw).verifying_key();
        NoteVerifyingKey::new(origin, VerifyingKey::Ed25519CosignatureV1(vk))
    }

    /// Helper to create a log NoteVerifyingKey for testing.
    fn make_log_vkey(origin: &str, raw: [u8; 32]) -> NoteVerifyingKey {
        let vk = SigningKey::from_bytes(&raw).verifying_key();
        NoteVerifyingKey::new(origin, VerifyingKey::Ed25519(vk))
    }

    /// All tests need at least one log key; this returns a minimal policy
    /// prefix with a log line.
    fn log_line(vkey: &NoteVerifyingKey) -> String {
        alloc::format!("log {}\n", vkey.to_vkey_string())
    }

    #[test]
    fn parse_empty_fails() {
        let err = Policy::parse("").unwrap_err();
        assert!(err.to_string().contains("no quorum line found"));
    }

    #[test]
    fn parse_no_log_keys_accepted() {
        let policy = Policy::parse("quorum none\n").unwrap();
        assert!(policy.log_keys().is_empty());
        assert!(policy.quorum.is_none());
    }

    #[test]
    fn parse_quorum_none() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let policy_text = alloc::format!("{}quorum none\n", log_line(&lkey));
        let policy = Policy::parse(&policy_text).unwrap();
        assert!(policy.quorum.is_none());
        assert_eq!(policy.log_keys().len(), 1);
        assert!(policy.check_quorum(&[]));
    }

    #[test]
    fn parse_log_key_stored() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let policy_text = alloc::format!("{}quorum none\n", log_line(&lkey));
        let policy = Policy::parse(&policy_text).unwrap();

        assert_eq!(policy.log_keys(), &[lkey]);
    }

    #[test]
    fn parse_multiple_log_keys() {
        let lkey1 = make_log_vkey("example.com/log", [0x01; 32]);
        let lkey2 = make_log_vkey("example.com/log", [0x02; 32]);
        let policy_text = alloc::format!("{}{}quorum none\n", log_line(&lkey1), log_line(&lkey2));
        let policy = Policy::parse(&policy_text).unwrap();
        assert_eq!(policy.log_keys(), &[lkey1, lkey2]);
    }

    #[test]
    fn parse_single_witness_quorum() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let wkey = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let vkey_str = wkey.to_vkey_string();
        let policy_text = alloc::format!(
            concat!("{}witness wit-1 {}\n", "quorum wit-1",),
            log_line(&lkey),
            vkey_str
        );
        let policy = Policy::parse(&policy_text).unwrap();

        // Quorum not satisfied without the witness.
        assert!(!policy.check_quorum(&[]));

        // Quorum satisfied with the witness.
        assert!(policy.check_quorum(&[&wkey]));
    }

    #[test]
    fn parse_group_threshold() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let w2 = make_witness_vkey("witness.example.com/w2", [0xBB; 32]);
        let w3 = make_witness_vkey("witness.example.com/w3", [0xCC; 32]);

        let policy_text = alloc::format!(
            concat!(
                "{}",
                "witness w1 {}\n",
                "witness w2 {}\n",
                "witness w3 {}\n",
                "group G 2 w1 w2 w3\n",
                "quorum G",
            ),
            log_line(&lkey),
            w1.to_vkey_string(),
            w2.to_vkey_string(),
            w3.to_vkey_string()
        );
        let policy = Policy::parse(&policy_text).unwrap();

        // 0 of 3 — not satisfied.
        assert!(!policy.check_quorum(&[]));

        // 1 of 3 — not satisfied.
        assert!(!policy.check_quorum(&[&w1]));

        // 2 of 3 — satisfied.
        assert!(policy.check_quorum(&[&w1, &w2]));
        assert!(policy.check_quorum(&[&w2, &w3]));
        assert!(policy.check_quorum(&[&w1, &w3]));

        // 3 of 3 — satisfied.
        assert!(policy.check_quorum(&[&w1, &w2, &w3]));
    }

    #[test]
    fn parse_group_any() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let w2 = make_witness_vkey("witness.example.com/w2", [0xBB; 32]);

        let policy_text = alloc::format!(
            concat!("{}", "witness w1 {}\n", "witness w2 {}\n", "group G any w1 w2\n", "quorum G",),
            log_line(&lkey),
            w1.to_vkey_string(),
            w2.to_vkey_string()
        );
        let policy = Policy::parse(&policy_text).unwrap();

        assert!(!policy.check_quorum(&[]));
        assert!(policy.check_quorum(&[&w1]));
        assert!(policy.check_quorum(&[&w2]));
    }

    #[test]
    fn parse_group_all() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let w2 = make_witness_vkey("witness.example.com/w2", [0xBB; 32]);

        let policy_text = alloc::format!(
            concat!("{}", "witness w1 {}\n", "witness w2 {}\n", "group G all w1 w2\n", "quorum G",),
            log_line(&lkey),
            w1.to_vkey_string(),
            w2.to_vkey_string()
        );
        let policy = Policy::parse(&policy_text).unwrap();

        assert!(!policy.check_quorum(&[&w1]));
        assert!(!policy.check_quorum(&[&w2]));
        assert!(policy.check_quorum(&[&w1, &w2]));
    }

    #[test]
    fn parse_nested_groups() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let w1 = make_witness_vkey("witness.example.com/w1", [0x01; 32]);
        let w2 = make_witness_vkey("witness.example.com/w2", [0x02; 32]);
        let w3 = make_witness_vkey("witness.example.com/w3", [0x03; 32]);
        let w4 = make_witness_vkey("witness.example.com/w4", [0x04; 32]);

        // Require: (w1 OR w2) AND (w3 AND w4)
        let policy_text = alloc::format!(
            concat!(
                "{}",
                "witness w1 {}\n",
                "witness w2 {}\n",
                "witness w3 {}\n",
                "witness w4 {}\n",
                "group left any w1 w2\n",
                "group right all w3 w4\n",
                "group root all left right\n",
                "quorum root\n",
            ),
            log_line(&lkey),
            w1.to_vkey_string(),
            w2.to_vkey_string(),
            w3.to_vkey_string(),
            w4.to_vkey_string(),
        );
        let policy = Policy::parse(&policy_text).unwrap();

        // Only left group satisfied.
        assert!(!policy.check_quorum(&[&w1]));

        // Only right group satisfied.
        assert!(!policy.check_quorum(&[&w3, &w4]));

        // Both groups satisfied.
        assert!(policy.check_quorum(&[&w1, &w3, &w4]));
        assert!(policy.check_quorum(&[&w2, &w3, &w4]));

        // Right group partially satisfied.
        assert!(!policy.check_quorum(&[&w1, &w3]));
    }

    #[test]
    fn parse_comments_and_blank_lines() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let policy_text = alloc::format!(
            concat!("# comment\n", "\n", "  # indented comment\n", "\n", "{}", "quorum none\n",),
            log_line(&lkey)
        );
        let policy = Policy::parse(&policy_text).unwrap();
        assert!(policy.quorum.is_none());
    }

    #[test]
    fn parse_duplicate_witness_name_fails() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let w2 = make_witness_vkey("witness.example.com/w2", [0xBB; 32]);
        let policy_text = alloc::format!(
            concat!("{}witness dup {}\n", "witness dup {}\n", "quorum none\n",),
            log_line(&lkey),
            w1.to_vkey_string(),
            w2.to_vkey_string()
        );
        let err = Policy::parse(&policy_text).unwrap_err();
        assert!(err.to_string().contains("duplicate name `dup`"));
    }

    #[test]
    fn parse_duplicate_quorum_fails() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let policy_text = alloc::format!(
            concat!("{}witness w1 {}\n", "quorum w1\n", "quorum w1\n",),
            log_line(&lkey),
            w1.to_vkey_string()
        );
        let err = Policy::parse(&policy_text).unwrap_err();
        assert!(err.to_string().contains("quorum already set"));
    }

    #[test]
    fn parse_unknown_quorum_name_fails() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let policy_text = alloc::format!("{}quorum unknown\n", log_line(&lkey));
        let err = Policy::parse(&policy_text).unwrap_err();
        assert!(err.to_string().contains("unknown quorum name `unknown`"));
    }

    #[test]
    fn parse_unknown_group_member_fails() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let policy_text = alloc::format!(
            concat!("{}witness w1 {}\n", "group G 1 w1 w2\n", "quorum G\n",),
            log_line(&lkey),
            w1.to_vkey_string()
        );
        let err = Policy::parse(&policy_text).unwrap_err();
        assert!(err.to_string().contains("unknown group member `w2`"));
    }

    #[test]
    fn parse_unknown_keyword_fails() {
        let err = Policy::parse("bogus foo bar\n").unwrap_err();
        assert!(err.to_string().contains("unknown keyword `bogus`"));
    }

    #[test]
    fn parse_non_cosignature_witness_fails() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        // A verifying key with type 0x01 (Ed25519Log) should be rejected
        // as a witness key.
        let vk = SigningKey::from_bytes(&[0xAA; 32]).verifying_key();
        let vkey = NoteVerifyingKey::new("witness.example.com/w1", VerifyingKey::Ed25519(vk));
        let policy_text = alloc::format!(
            concat!("{}witness w1 {}\n", "quorum w1\n",),
            log_line(&lkey),
            vkey.to_vkey_string()
        );
        let err = Policy::parse(&policy_text).unwrap_err();
        assert!(err.to_string().contains("cosignature type (0x04 or 0x06)"));
    }

    #[test]
    fn parse_cosignature_v1_log_fails() {
        // A log verifying key with type 0x04 (Ed25519Cosigner) should be
        // rejected as a log key.
        let vk = SigningKey::from_bytes(&[0x01; 32]).verifying_key();
        let vkey = NoteVerifyingKey::new("example.com/log", VerifyingKey::Ed25519CosignatureV1(vk));
        let policy_text = alloc::format!("log {}\nquorum none\n", vkey.to_vkey_string());
        let err = Policy::parse(&policy_text).unwrap_err();
        assert!(err.to_string().contains("Ed25519 (0x01) or ML-DSA-44 (0x06)"));
    }

    #[test]
    fn parse_ml_dsa_log_key_succeeds() {
        use oak_crypto_tink::ml_dsa_44;

        let kp = ml_dsa_44::generate_key_pair().unwrap();
        let lkey = NoteVerifyingKey::new(
            "example.com/log",
            VerifyingKey::MlDsa44SubtreeV1(kp.verifying_key().clone()),
        );
        let policy_text = alloc::format!("{}quorum none\n", log_line(&lkey));
        let policy = Policy::parse(&policy_text).unwrap();
        assert_eq!(policy.log_keys().len(), 1);
    }

    #[test]
    fn parse_invalid_witness_key_fails() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let policy_text =
            alloc::format!("{}witness w1 not-a-valid-vkey\nquorum w1\n", log_line(&lkey));
        let err = Policy::parse(&policy_text).unwrap_err();
        assert!(err.to_string().contains("C2SP verifying key string"));
    }

    #[test]
    fn parse_invalid_log_key_fails() {
        let policy_text = "log not-a-valid-vkey\nquorum none\n";
        let err = Policy::parse(policy_text).unwrap_err();
        assert!(err.to_string().contains("C2SP verifying key string"));
    }

    #[test]
    fn parse_invalid_log_arg_count() {
        let err = Policy::parse(concat!("log\n", "quorum none\n",)).unwrap_err();
        assert!(err.to_string().contains("expected 1 or 2 arguments, got 0"));
    }

    #[test]
    fn parse_invalid_witness_arg_count() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let err = Policy::parse(&alloc::format!("{}witness w1\nquorum none\n", log_line(&lkey)))
            .unwrap_err();
        assert!(err.to_string().contains("expected 2 or 3 arguments, got 1"));
    }

    #[test]
    fn parse_invalid_group_arg_count() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let err = Policy::parse(&alloc::format!("{}group G any\nquorum none\n", log_line(&lkey)))
            .unwrap_err();
        assert!(err.to_string().contains("expected at least 3 arguments, got 2"));
    }

    #[test]
    fn parse_invalid_quorum_arg_count() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let err = Policy::parse(&alloc::format!("{}quorum\n", log_line(&lkey))).unwrap_err();
        assert!(err.to_string().contains("expected exactly one argument"));

        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let err = Policy::parse(&alloc::format!(
            concat!("{}witness w1 {}\n", "quorum w1 extra\n",),
            log_line(&lkey),
            w1.to_vkey_string()
        ))
        .unwrap_err();
        assert!(err.to_string().contains("expected exactly one argument"));
    }

    #[test]
    fn parse_invalid_group_threshold() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let err = Policy::parse(&alloc::format!(
            concat!("{}witness w1 {}\n", "group G xyz w1\n", "quorum G\n",),
            log_line(&lkey),
            w1.to_vkey_string()
        ))
        .unwrap_err();
        assert!(err.to_string().contains("invalid threshold `xyz`"));
    }

    #[test]
    fn unrelated_witness_does_not_satisfy_quorum() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let w_other = make_witness_vkey("witness.example.com/other", [0xFF; 32]);

        let policy_text = alloc::format!(
            concat!("{}witness w1 {}\n", "quorum w1\n",),
            log_line(&lkey),
            w1.to_vkey_string()
        );
        let policy = Policy::parse(&policy_text).unwrap();

        // An unrelated witness key should not satisfy the quorum.
        assert!(!policy.check_quorum(&[&w_other]));
    }

    #[test]
    fn parse_duplicate_log_key_fails() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        // Same underlying key, even with a different origin name.
        let lkey2 = NoteVerifyingKey::new("other.com/log", lkey.verifying_key.clone());
        let policy_text = alloc::format!(
            "log {}\nlog {}\nquorum none\n",
            lkey.to_vkey_string(),
            lkey2.to_vkey_string()
        );
        let err = Policy::parse(&policy_text).unwrap_err();
        assert!(err.to_string().contains("duplicate log key"));
    }

    #[test]
    fn parse_witness_name_none_fails() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let policy_text = alloc::format!(
            "{}witness none {}\nquorum none\n",
            log_line(&lkey),
            w1.to_vkey_string()
        );
        let err = Policy::parse(&policy_text).unwrap_err();
        assert!(err.to_string().contains("`none` is a reserved name"));
    }

    #[test]
    fn parse_group_name_none_fails() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let policy_text = alloc::format!(
            concat!("{}witness w1 {}\n", "group none any w1\n", "quorum w1\n",),
            log_line(&lkey),
            w1.to_vkey_string()
        );
        let err = Policy::parse(&policy_text).unwrap_err();
        assert!(err.to_string().contains("`none` is a reserved name"));
    }

    #[test]
    fn parse_threshold_zero_fails() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let policy_text = alloc::format!(
            concat!("{}witness w1 {}\n", "group G 0 w1\n", "quorum G\n",),
            log_line(&lkey),
            w1.to_vkey_string()
        );
        let err = Policy::parse(&policy_text).unwrap_err();
        assert!(err.to_string().contains("threshold 0 out of range for group of size 1"));
    }

    #[test]
    fn parse_threshold_exceeds_n_fails() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let policy_text = alloc::format!(
            concat!("{}witness w1 {}\n", "group G 2 w1\n", "quorum G\n",),
            log_line(&lkey),
            w1.to_vkey_string()
        );
        let err = Policy::parse(&policy_text).unwrap_err();
        assert!(err.to_string().contains("threshold 2 out of range for group of size 1"));
    }

    #[test]
    fn parse_duplicate_group_member_fails() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let policy_text = alloc::format!(
            concat!("{}witness w1 {}\n", "group G 1 w1 w1\n", "quorum G\n",),
            log_line(&lkey),
            w1.to_vkey_string()
        );
        let err = Policy::parse(&policy_text).unwrap_err();
        assert!(err.to_string().contains("duplicate group member `w1`"));
    }

    #[test]
    fn parse_duplicate_witness_key_fails() {
        let lkey = make_log_vkey("example.com/log", [0x01; 32]);
        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        // Same underlying key with a different name.
        let w2 = NoteVerifyingKey::new("witness.example.com/w2", w1.verifying_key.clone());
        let policy_text = alloc::format!(
            concat!("{}witness w1 {}\n", "witness w2 {}\n", "quorum none\n",),
            log_line(&lkey),
            w1.to_vkey_string(),
            w2.to_vkey_string()
        );
        let err = Policy::parse(&policy_text).unwrap_err();
        assert!(err.to_string().contains("duplicate witness key"));
    }
}
