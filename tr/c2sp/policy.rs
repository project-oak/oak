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

//! Witness quorum policies for C2SP transparency log proofs.
//!
//! A [`WitnessPolicy`] defines which witnesses are known and what quorum of
//! witness cosignatures is required for a checkpoint to be considered valid.
//!
//! Policies are parsed from the
//! [sigsum policy file format](https://git.glasklar.is/sigsum/core/sigsum-go/-/blob/main/doc/policy.md),
//! with the additional requirement that witness public keys must be provided as
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

use thiserror::Error;

use crate::note::{NoteVerifyingKey, SignatureType};

/// A policy-local name identifying a witness or group within a
/// [`WitnessPolicy`].
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

/// Error type for witness policy parsing.
#[derive(Debug, Error)]
pub enum WitnessPolicyError {
    #[error("line {line}: {reason}")]
    Parse { line: usize, reason: String },
}

/// A witness quorum policy where witnesses are identified by C2SP verifying
/// keys.
///
/// The policy specifies a set of known witnesses and the quorum rule that
/// determines whether enough witness cosignatures are present for a checkpoint
/// to be considered valid.
///
/// Witness public keys in the policy file must be
/// [C2SP verifying key strings](https://c2sp.org/signed-note#verifier-keys)
/// with signature type `0x04` ([`SignatureType::CosignatureV1`]).
#[derive(Debug)]
pub struct WitnessPolicy {
    /// Named quorum entries (witnesses and groups), indexed by policy-local
    /// name.
    quorums: BTreeMap<QuorumName, Quorum>,
    /// The root quorum name. `None` means `quorum none` — no witnesses
    /// required.
    quorum: Option<QuorumName>,
}

/// Internal representation of a quorum tree node.
#[derive(Debug)]
enum Quorum {
    /// A single witness, identified by its C2SP verifying key.
    Witness(NoteVerifyingKey),
    /// A threshold group: at least `k` of `members` must be satisfied.
    Group { k: usize, members: Vec<QuorumName> },
}

impl WitnessPolicy {
    /// Parses a witness policy from its text representation.
    ///
    /// Follows the
    /// [sigsum policy format](https://git.glasklar.is/sigsum/core/sigsum-go/-/blob/main/doc/policy.md),
    /// with the requirement that witness public keys are specified as
    /// [C2SP verifying key strings](https://c2sp.org/signed-note#verifier-keys).
    ///
    /// `log` lines are accepted for format compatibility but are not stored.
    pub fn parse(data: &str) -> Result<Self, WitnessPolicyError> {
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
                    // Accept log lines for format compatibility, but ignore
                    // them. The log key is provided separately to
                    // TLogProof::verify.
                    let nargs = tokens.len() - 1;
                    if !(1..=2).contains(&nargs) {
                        return Err(WitnessPolicyError::Parse {
                            line: lineno + 1,
                            reason: alloc::format!(
                                "invalid log rule: expected 1 or 2 arguments, got {nargs}"
                            ),
                        });
                    }
                }
                "witness" => {
                    let nargs = tokens.len() - 1;
                    if !(2..=3).contains(&nargs) {
                        return Err(WitnessPolicyError::Parse {
                            line: lineno + 1,
                            reason: alloc::format!(
                                "invalid witness rule: expected 2 or 3 arguments, got {nargs}"
                            ),
                        });
                    }
                    let name = tokens[1];
                    let vkey_str = tokens[2];

                    // Parse the vkey as a C2SP verifying key.
                    let vkey = NoteVerifyingKey::parse(vkey_str).map_err(|_| {
                        WitnessPolicyError::Parse {
                            line: lineno + 1,
                            reason: "witness key must be a C2SP verifying key string".into(),
                        }
                    })?;

                    // Validate: witness keys must be cosignature type (0x04).
                    if vkey.signature_type != SignatureType::CosignatureV1 {
                        return Err(WitnessPolicyError::Parse {
                            line: lineno + 1,
                            reason: "witness key must have cosignature type (0x04)".into(),
                        });
                    }

                    let name = QuorumName::new(name);
                    if quorums.contains_key(&name) {
                        return Err(WitnessPolicyError::Parse {
                            line: lineno + 1,
                            reason: alloc::format!("duplicate name `{name}`"),
                        });
                    }

                    quorums.insert(name, Quorum::Witness(vkey));
                }
                "group" => {
                    let nargs = tokens.len() - 1;
                    if nargs < 3 {
                        return Err(WitnessPolicyError::Parse {
                            line: lineno + 1,
                            reason: alloc::format!(
                                "invalid group rule: expected at least 3 arguments, got {nargs}"
                            ),
                        });
                    }
                    let name = tokens[1];
                    let k_str = tokens[2];
                    let members: Vec<QuorumName> =
                        tokens[3..].iter().map(|s| QuorumName::new(s)).collect();

                    let k = parse_threshold(k_str, members.len()).ok_or_else(|| {
                        WitnessPolicyError::Parse {
                            line: lineno + 1,
                            reason: alloc::format!(
                                "invalid group rule: cannot parse `{k_str}` as a threshold"
                            ),
                        }
                    })?;

                    let name = QuorumName::new(name);
                    if quorums.contains_key(&name) {
                        return Err(WitnessPolicyError::Parse {
                            line: lineno + 1,
                            reason: alloc::format!("duplicate name `{name}`"),
                        });
                    }

                    // Validate all members refer to previously defined names.
                    for member in &members {
                        if !quorums.contains_key(member) {
                            return Err(WitnessPolicyError::Parse {
                                line: lineno + 1,
                                reason: alloc::format!("unknown group member `{member}`"),
                            });
                        }
                    }

                    quorums.insert(name, Quorum::Group { k, members });
                }
                "quorum" => {
                    if tokens.len() != 2 {
                        return Err(WitnessPolicyError::Parse {
                            line: lineno + 1,
                            reason: "invalid quorum rule: expected exactly one argument".into(),
                        });
                    }
                    if quorum_set {
                        return Err(WitnessPolicyError::Parse {
                            line: lineno + 1,
                            reason: "quorum already set".into(),
                        });
                    }
                    quorum_set = true;

                    let name = tokens[1];
                    if name != "none" {
                        let name = QuorumName::new(name);
                        if !quorums.contains_key(&name) {
                            return Err(WitnessPolicyError::Parse {
                                line: lineno + 1,
                                reason: alloc::format!("unknown quorum name `{name}`"),
                            });
                        }
                        root_quorum = Some(name);
                    }
                }
                unknown => {
                    return Err(WitnessPolicyError::Parse {
                        line: lineno + 1,
                        reason: alloc::format!("unknown keyword `{unknown}`"),
                    });
                }
            }
        }

        if !quorum_set {
            return Err(WitnessPolicyError::Parse {
                line: data.lines().count(),
                reason: "no quorum line found".into(),
            });
        }

        Ok(WitnessPolicy { quorums, quorum: root_quorum })
    }

    /// Returns a policy with no witness requirements (`quorum none`).
    pub fn empty() -> Self {
        Self::parse("quorum none\n").expect("valid policy format")
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
            Quorum::Witness(witness_key) => verified_keys.iter().any(|k| *k == witness_key),
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

/// Parses a threshold value: `"any"` → 1, `"all"` → n, or a numeric value.
fn parse_threshold(s: &str, n: usize) -> Option<usize> {
    match s {
        "any" => Some(1),
        "all" => Some(n),
        _ => s.parse().ok(),
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
        NoteVerifyingKey::from_parts(origin, SignatureType::CosignatureV1, vk)
    }

    #[test]
    fn parse_empty_fails() {
        let err = WitnessPolicy::parse("").unwrap_err();
        assert!(err.to_string().contains("no quorum line found"));
    }

    #[test]
    fn parse_quorum_none() {
        let policy = WitnessPolicy::parse("quorum none\n").unwrap();
        assert!(policy.quorum.is_none());
        assert!(policy.check_quorum(&[]));
    }

    #[test]
    fn parse_single_witness_quorum() {
        let wkey = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let vkey_str = wkey.to_vkey_string();
        let policy_text = alloc::format!(concat!("witness wit-1 {}\n", "quorum wit-1",), vkey_str);
        let policy = WitnessPolicy::parse(&policy_text).unwrap();

        // Quorum not satisfied without the witness.
        assert!(!policy.check_quorum(&[]));

        // Quorum satisfied with the witness.
        assert!(policy.check_quorum(&[&wkey]));
    }

    #[test]
    fn parse_group_threshold() {
        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let w2 = make_witness_vkey("witness.example.com/w2", [0xBB; 32]);
        let w3 = make_witness_vkey("witness.example.com/w3", [0xCC; 32]);

        let policy_text = alloc::format!(
            concat!(
                "witness w1 {}\n",
                "witness w2 {}\n",
                "witness w3 {}\n",
                "group G 2 w1 w2 w3\n",
                "quorum G",
            ),
            w1.to_vkey_string(),
            w2.to_vkey_string(),
            w3.to_vkey_string()
        );
        let policy = WitnessPolicy::parse(&policy_text).unwrap();

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
        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let w2 = make_witness_vkey("witness.example.com/w2", [0xBB; 32]);

        let policy_text = alloc::format!(
            concat!("witness w1 {}\n", "witness w2 {}\n", "group G any w1 w2\n", "quorum G",),
            w1.to_vkey_string(),
            w2.to_vkey_string()
        );
        let policy = WitnessPolicy::parse(&policy_text).unwrap();

        assert!(!policy.check_quorum(&[]));
        assert!(policy.check_quorum(&[&w1]));
        assert!(policy.check_quorum(&[&w2]));
    }

    #[test]
    fn parse_group_all() {
        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let w2 = make_witness_vkey("witness.example.com/w2", [0xBB; 32]);

        let policy_text = alloc::format!(
            concat!("witness w1 {}\n", "witness w2 {}\n", "group G all w1 w2\n", "quorum G",),
            w1.to_vkey_string(),
            w2.to_vkey_string()
        );
        let policy = WitnessPolicy::parse(&policy_text).unwrap();

        assert!(!policy.check_quorum(&[&w1]));
        assert!(!policy.check_quorum(&[&w2]));
        assert!(policy.check_quorum(&[&w1, &w2]));
    }

    #[test]
    fn parse_nested_groups() {
        let w1 = make_witness_vkey("witness.example.com/w1", [0x01; 32]);
        let w2 = make_witness_vkey("witness.example.com/w2", [0x02; 32]);
        let w3 = make_witness_vkey("witness.example.com/w3", [0x03; 32]);
        let w4 = make_witness_vkey("witness.example.com/w4", [0x04; 32]);

        // Require: (w1 OR w2) AND (w3 AND w4)
        let policy_text = alloc::format!(
            concat!(
                "witness w1 {}\n",
                "witness w2 {}\n",
                "witness w3 {}\n",
                "witness w4 {}\n",
                "group left any w1 w2\n",
                "group right all w3 w4\n",
                "group root all left right\n",
                "quorum root\n",
            ),
            w1.to_vkey_string(),
            w2.to_vkey_string(),
            w3.to_vkey_string(),
            w4.to_vkey_string(),
        );
        let policy = WitnessPolicy::parse(&policy_text).unwrap();

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
    fn parse_log_lines_ignored() {
        // Log lines are accepted but not stored.
        let policy_text = "log some.log.example.com+abcd1234+AAAA\nquorum none\n";
        let policy = WitnessPolicy::parse(policy_text).unwrap();
        assert!(policy.quorum.is_none());
    }

    #[test]
    fn parse_comments_and_blank_lines() {
        let policy_text =
            concat!("# comment\n", "\n", "  # indented comment\n", "\n", "quorum none\n",);
        let policy = WitnessPolicy::parse(policy_text).unwrap();
        assert!(policy.quorum.is_none());
    }

    #[test]
    fn parse_duplicate_witness_name_fails() {
        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let w2 = make_witness_vkey("witness.example.com/w2", [0xBB; 32]);
        let policy_text = alloc::format!(
            concat!("witness dup {}\n", "witness dup {}\n", "quorum none\n",),
            w1.to_vkey_string(),
            w2.to_vkey_string()
        );
        let err = WitnessPolicy::parse(&policy_text).unwrap_err();
        assert!(err.to_string().contains("duplicate name `dup`"));
    }

    #[test]
    fn parse_duplicate_quorum_fails() {
        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let policy_text = alloc::format!(
            concat!("witness w1 {}\n", "quorum w1\n", "quorum w1\n",),
            w1.to_vkey_string()
        );
        let err = WitnessPolicy::parse(&policy_text).unwrap_err();
        assert!(err.to_string().contains("quorum already set"));
    }

    #[test]
    fn parse_unknown_quorum_name_fails() {
        let err = WitnessPolicy::parse("quorum unknown\n").unwrap_err();
        assert!(err.to_string().contains("unknown quorum name `unknown`"));
    }

    #[test]
    fn parse_unknown_group_member_fails() {
        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let policy_text = alloc::format!(
            concat!("witness w1 {}\n", "group G 1 w1 w2\n", "quorum G\n",),
            w1.to_vkey_string()
        );
        let err = WitnessPolicy::parse(&policy_text).unwrap_err();
        assert!(err.to_string().contains("unknown group member `w2`"));
    }

    #[test]
    fn parse_unknown_keyword_fails() {
        let err = WitnessPolicy::parse("bogus foo bar\n").unwrap_err();
        assert!(err.to_string().contains("unknown keyword `bogus`"));
    }

    #[test]
    fn parse_non_cosignature_witness_fails() {
        // A verifying key with type 0x01 (Ed25519) should be rejected.
        let vk = SigningKey::from_bytes(&[0xAA; 32]).verifying_key();
        let vkey =
            NoteVerifyingKey::from_parts("witness.example.com/w1", SignatureType::Ed25519, vk);
        let policy_text =
            alloc::format!(concat!("witness w1 {}\n", "quorum w1\n",), vkey.to_vkey_string());
        let err = WitnessPolicy::parse(&policy_text).unwrap_err();
        assert!(err.to_string().contains("cosignature type (0x04)"));
    }

    #[test]
    fn parse_invalid_witness_key_fails() {
        let policy_text = concat!("witness w1 not-a-valid-vkey\n", "quorum w1\n",);
        let err = WitnessPolicy::parse(policy_text).unwrap_err();
        assert!(err.to_string().contains("C2SP verifying key string"));
    }

    #[test]
    fn parse_invalid_log_arg_count() {
        let err = WitnessPolicy::parse(concat!("log\n", "quorum none\n",)).unwrap_err();
        assert!(err.to_string().contains("expected 1 or 2 arguments, got 0"));
    }

    #[test]
    fn parse_invalid_witness_arg_count() {
        let err = WitnessPolicy::parse(concat!("witness w1\n", "quorum none\n",)).unwrap_err();
        assert!(err.to_string().contains("expected 2 or 3 arguments, got 1"));
    }

    #[test]
    fn parse_invalid_group_arg_count() {
        let err = WitnessPolicy::parse(concat!("group G any\n", "quorum none\n",)).unwrap_err();
        assert!(err.to_string().contains("expected at least 3 arguments, got 2"));
    }

    #[test]
    fn parse_invalid_quorum_arg_count() {
        let err = WitnessPolicy::parse("quorum\n").unwrap_err();
        assert!(err.to_string().contains("expected exactly one argument"));

        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let err = WitnessPolicy::parse(&alloc::format!(
            concat!("witness w1 {}\n", "quorum w1 extra\n",),
            w1.to_vkey_string()
        ))
        .unwrap_err();
        assert!(err.to_string().contains("expected exactly one argument"));
    }

    #[test]
    fn parse_invalid_group_threshold() {
        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let err = WitnessPolicy::parse(&alloc::format!(
            concat!("witness w1 {}\n", "group G xyz w1\n", "quorum G\n",),
            w1.to_vkey_string()
        ))
        .unwrap_err();
        assert!(err.to_string().contains("cannot parse `xyz` as a threshold"));
    }

    #[test]
    fn unrelated_witness_does_not_satisfy_quorum() {
        let w1 = make_witness_vkey("witness.example.com/w1", [0xAA; 32]);
        let w_other = make_witness_vkey("witness.example.com/other", [0xFF; 32]);

        let policy_text =
            alloc::format!(concat!("witness w1 {}\n", "quorum w1\n",), w1.to_vkey_string());
        let policy = WitnessPolicy::parse(&policy_text).unwrap();

        // An unrelated witness key should not satisfy the quorum.
        assert!(!policy.check_quorum(&[&w_other]));
    }
}
