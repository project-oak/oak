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

//! Information Flow Control (IFC) label types for cleanroom.
//!
//! # Model
//!
//! Cleanroom uses a **dual-component label** model inspired by the
//! [Decentralized Label Model (DLM)][dlm] and matching the reference
//! implementation at `mcp/ifc/labels/label.py`.
//!
//! A [`Label`] is a pair `(secrecy, integrity)` where both components
//! are sets of [`Principal`]s:
//!
//! - **Secrecy**: more principals = more restricted (subset ordering). Data
//!   labeled `{github, tzn}` requires authority over *both* to declassify.
//! - **Integrity**: more principals = more trusted (reversed ordering). Data
//!   vouched for by `{github}` can flow to channels requiring `{github}`
//!   integrity or lower.
//!
//! ## Lattice operations
//!
//! | Operation | Secrecy | Integrity |
//! |-----------|---------|-----------|
//! | **Join** (read two inputs) | `S₁ ∪ S₂` | `I₁ ∩ I₂` |
//! | **Flows-to** | `self.S ⊆ target.S` | `target.I ⊆ self.I` |
//! | **Declassify** | Remove from S | _(unchanged)_ |
//! | **Endorse** | _(unchanged)_ | Add to I |
//!
//! ## Principals
//!
//! A [`Principal`] is an atom of both lattice dimensions.  There are
//! three kinds (distinguished in `principals.toml`, uniform here):
//!
//! - **Named**: abstract identities (`tzn`, `github`).
//! - **SSH key**: cryptographic identity for a human or machine.
//! - **Module**: code identity (Wasm content digest).
//!
//! Authority flows via the "speaks for" relation ([Lampson et al.
//! 1992][lampson]).
//!
//! ## Robust declassification
//!
//! Naïve declassification is dangerous: if a module processes both a
//! secret and attacker-controlled input, the attacker can steer *what*
//! gets declassified.  [Zdancewic & Myers (2001)][robust] showed that
//! declassification should only be allowed when the integrity of the
//! computation is high — i.e. the decision was not influenced by
//! low-integrity data.
//!
//! [dlm]: https://www.cs.cornell.edu/andru/papers/iflow-sosp97/
//! [robust]: https://www.cis.upenn.edu/~stevez/papers/ZM01b.pdf
//! [lampson]: https://doi.org/10.1145/138873.138874

use std::{collections::BTreeSet, fmt};

use serde::{Deserialize, Serialize};

// ── Principal ────────────────────────────────────────────────────

/// A principal identity — the atom of both the secrecy and integrity
/// lattices.
///
/// The value is the principal's unique name from `principals.toml`.
/// Named principals like `"tzn"` and `"github"` are abstract
/// identities.  SSH keys and modules are concrete principals that
/// speak for named ones via explicit delegation.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Principal(String);

impl Principal {
    /// Creates a principal with the given name.
    pub fn new(name: impl Into<String>) -> Self {
        Self(name.into())
    }

    /// Returns the principal's name.
    pub fn name(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Principal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// ── Label ────────────────────────────────────────────────────────

/// A dual-component IFC label: (secrecy, integrity).
///
/// This matches the `Label` class in `mcp/ifc/labels/label.py`.
///
/// - **Secrecy** (`S`): set of principals.  More = more restricted. Ordering:
///   `S₁ ⊑ S₂` iff `S₁ ⊆ S₂`.
/// - **Integrity** (`I`): set of principals.  More = more trusted. Ordering:
///   `I₁ ⊑ I₂` iff `I₂ ⊆ I₁` (reversed).
///
/// Combined flows-to: `L₁` can flow to `L₂` iff
/// `L₁.S ⊆ L₂.S` AND `L₂.I ⊆ L₁.I`.
#[derive(Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Label {
    /// Secrecy component: who must authorize release.
    secrecy: BTreeSet<Principal>,
    /// Integrity component: who vouches for this data.
    integrity: BTreeSet<Principal>,
}

impl Label {
    /// Creates a label with explicit secrecy and integrity.
    pub fn new(
        secrecy: impl IntoIterator<Item = Principal>,
        integrity: impl IntoIterator<Item = Principal>,
    ) -> Self {
        Self { secrecy: secrecy.into_iter().collect(), integrity: integrity.into_iter().collect() }
    }

    /// The public (bottom) label: no secrecy, no integrity.
    pub fn public() -> Self {
        Self::default()
    }

    /// A label with secrecy principals only (no integrity).
    pub fn secret(principals: impl IntoIterator<Item = Principal>) -> Self {
        Self { secrecy: principals.into_iter().collect(), integrity: BTreeSet::new() }
    }

    /// A label with integrity principals only (no secrecy).
    pub fn trusted(principals: impl IntoIterator<Item = Principal>) -> Self {
        Self { secrecy: BTreeSet::new(), integrity: principals.into_iter().collect() }
    }

    /// Returns the join (least upper bound) of two labels.
    ///
    /// Secrecy: union (taint grows).
    /// Integrity: intersection (trust degrades).
    pub fn join(&self, other: &Label) -> Label {
        Label {
            secrecy: self.secrecy.union(&other.secrecy).cloned().collect(),
            integrity: self.integrity.intersection(&other.integrity).cloned().collect(),
        }
    }

    /// Checks whether data at this label can flow to a channel with
    /// `target` label.
    ///
    /// Flow is allowed iff:
    /// - `self.secrecy ⊆ target.secrecy` (no write-down)
    /// - `target.integrity ⊆ self.integrity` (no read-down)
    pub fn flows_to(&self, target: &Label) -> Result<(), FlowError> {
        let excess_secrecy: BTreeSet<Principal> =
            self.secrecy.difference(&target.secrecy).cloned().collect();
        let missing_integrity: BTreeSet<Principal> =
            target.integrity.difference(&self.integrity).cloned().collect();

        if excess_secrecy.is_empty() && missing_integrity.is_empty() {
            Ok(())
        } else {
            Err(FlowError { excess_secrecy, missing_integrity })
        }
    }

    /// Checks if data at this label can flow to `target` after
    /// exercising the given declassification and endorsement
    /// privilege.
    ///
    /// This applies privilege per-operation without mutating any
    /// label.  The `declassify` set removes secrecy principals from
    /// `self` and the `endorse` set adds integrity principals to
    /// `self` before performing the flow check.
    ///
    /// Returns an error if the privilege does not cover the
    /// requested principals or if the adjusted label still does not
    /// flow.
    pub fn flows_to_with_privilege(
        &self,
        target: &Label,
        privilege: &Privilege,
        declassify: &BTreeSet<Principal>,
        endorse: &BTreeSet<Principal>,
    ) -> Result<(), FlowError> {
        // Verify privilege covers all requested operations.
        let uncovered_declass = privilege.uncovered_declassify(declassify);
        let uncovered_endorse = privilege.uncovered_endorse(endorse);
        if !uncovered_declass.is_empty() || !uncovered_endorse.is_empty() {
            return Err(FlowError {
                excess_secrecy: uncovered_declass,
                missing_integrity: uncovered_endorse,
            });
        }

        // Apply privilege: declassify removes secrecy, endorse adds integrity.
        let adjusted = self.declassify(declassify).endorse(endorse);
        adjusted.flows_to(target)
    }

    /// Checks if data at this label can flow to `target` after
    /// declassifying (removing secrecy) using the given privilege.
    ///
    /// Use this for **writes / output**: data leaves the computation
    /// toward a less-secret destination. Declassification lowers
    /// secrecy; endorsement is not applied.
    pub fn flows_to_declassifying(
        &self,
        target: &Label,
        privilege: &Privilege,
    ) -> Result<(), FlowError> {
        let adjusted = self.declassify(privilege.declassify_set());
        adjusted.flows_to(target)
    }

    /// Checks if data at this label can flow to `target` after
    /// endorsing (raising integrity) using the given privilege.
    ///
    /// Use this for **reads / input**: data enters the computation
    /// from a less-trusted source. Endorsement raises integrity;
    /// declassification is not applied.
    pub fn flows_to_endorsing(
        &self,
        target: &Label,
        privilege: &Privilege,
    ) -> Result<(), FlowError> {
        let adjusted = self.endorse(privilege.endorse_set());
        adjusted.flows_to(target)
    }

    /// Returns `true` if the label is public (no secrecy, no integrity).
    pub fn is_public(&self) -> bool {
        self.secrecy.is_empty() && self.integrity.is_empty()
    }

    /// Returns `true` if the secrecy component is empty.
    pub fn is_declassified(&self) -> bool {
        self.secrecy.is_empty()
    }

    /// Returns a new label with the given secrecy principals removed.
    pub fn declassify(&self, principals: &BTreeSet<Principal>) -> Label {
        Label {
            secrecy: self.secrecy.difference(principals).cloned().collect(),
            integrity: self.integrity.clone(),
        }
    }

    /// Returns a new label with the given integrity principals added.
    pub fn endorse(&self, principals: &BTreeSet<Principal>) -> Label {
        Label {
            secrecy: self.secrecy.clone(),
            integrity: self.integrity.union(principals).cloned().collect(),
        }
    }

    /// Returns the secrecy principal names as strings.
    pub fn secrecy_names(&self) -> Vec<String> {
        self.secrecy.iter().map(|p| p.name().to_string()).collect()
    }

    /// Returns the secrecy principal set.
    pub fn secrecy_set(&self) -> &BTreeSet<Principal> {
        &self.secrecy
    }

    /// Returns the integrity principal names as strings.
    pub fn integrity_names(&self) -> Vec<String> {
        self.integrity.iter().map(|p| p.name().to_string()).collect()
    }

    /// Returns the integrity principal set.
    pub fn integrity_set(&self) -> &BTreeSet<Principal> {
        &self.integrity
    }
}

impl fmt::Debug for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Label(S={:?}, I={:?})", self.secrecy_names(), self.integrity_names())
    }
}

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = format_principal_set(&self.secrecy);
        let i = format_principal_set(&self.integrity);
        write!(f, "(S={s}, I={i})")
    }
}

fn format_principal_set(set: &BTreeSet<Principal>) -> String {
    if set.is_empty() {
        "∅".to_string()
    } else {
        let names: Vec<_> = set.iter().map(|p| p.name()).collect();
        format!("{{{}}}", names.join(", "))
    }
}

// ── Privilege ────────────────────────────────────────────────────

/// Authority to declassify secrecy principals and endorse integrity
/// principals.
///
/// This is the unified privilege type, replacing the separate
/// `DeclassificationPrivilege` and `EndorsementPrivilege`.
/// Matches `mcp/ifc/labels/privilege.py::Privilege`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Privilege {
    /// Principals whose secrecy this module can remove.
    declassify: BTreeSet<Principal>,
    /// Principals whose integrity this module can restore.
    endorse: BTreeSet<Principal>,
}

impl Privilege {
    /// No privilege at all.
    pub fn none() -> Self {
        Self::default()
    }

    /// Privilege to declassify the given principals.
    pub fn for_declassification(ps: impl IntoIterator<Item = Principal>) -> Self {
        Self { declassify: ps.into_iter().collect(), endorse: BTreeSet::new() }
    }

    /// Privilege to endorse the given principals.
    pub fn for_endorsement(ps: impl IntoIterator<Item = Principal>) -> Self {
        Self { declassify: BTreeSet::new(), endorse: ps.into_iter().collect() }
    }

    /// Full privilege for the given principals (both declassify and endorse).
    pub fn full(ps: impl IntoIterator<Item = Principal>) -> Self {
        let set: BTreeSet<Principal> = ps.into_iter().collect();
        Self { declassify: set.clone(), endorse: set }
    }

    /// Creates a privilege with explicit sets.
    pub fn new(
        declassify: impl IntoIterator<Item = Principal>,
        endorse: impl IntoIterator<Item = Principal>,
    ) -> Self {
        Self {
            declassify: declassify.into_iter().collect(),
            endorse: endorse.into_iter().collect(),
        }
    }

    /// Returns `true` if every principal in `requested` is covered
    /// by the declassification privilege.
    pub fn covers_declassify(&self, requested: &BTreeSet<Principal>) -> bool {
        requested.is_subset(&self.declassify)
    }

    /// Returns the declassification principals not covered.
    pub fn uncovered_declassify(&self, requested: &BTreeSet<Principal>) -> BTreeSet<Principal> {
        requested.difference(&self.declassify).cloned().collect()
    }

    /// Returns `true` if every principal in `requested` is covered
    /// by the endorsement privilege.
    pub fn covers_endorse(&self, requested: &BTreeSet<Principal>) -> bool {
        requested.is_subset(&self.endorse)
    }

    /// Returns the endorsement principals not covered.
    pub fn uncovered_endorse(&self, requested: &BTreeSet<Principal>) -> BTreeSet<Principal> {
        requested.difference(&self.endorse).cloned().collect()
    }

    /// Returns the declassification set.
    pub fn declassify_set(&self) -> &BTreeSet<Principal> {
        &self.declassify
    }

    /// Returns the endorsement set.
    pub fn endorse_set(&self) -> &BTreeSet<Principal> {
        &self.endorse
    }

    /// Merges another privilege into this one (union of both sets).
    pub fn merge(&self, other: &Privilege) -> Privilege {
        Privilege {
            declassify: self.declassify.union(&other.declassify).cloned().collect(),
            endorse: self.endorse.union(&other.endorse).cloned().collect(),
        }
    }
}

// ── ComputationLabel ─────────────────────────────────────────────

/// Tracks the current IFC label for a single module invocation.
///
/// Created at the start of each invocation.  The label's secrecy
/// grows via [`observe`](Self::observe) and shrinks via
/// [`declassify`](Self::declassify).  Integrity shrinks via
/// [`observe`](Self::observe) and grows via
/// [`endorse`](Self::endorse).
pub struct ComputationLabel {
    /// The current computation label.
    label: Label,
}

impl ComputationLabel {
    /// Creates a computation label with the given initial label.
    pub fn new(initial: Label) -> Self {
        Self { label: initial }
    }

    /// Creates a public (untainted, untrusted) computation label.
    pub fn untainted() -> Self {
        Self { label: Label::public() }
    }

    /// Records that the module observed data with the given label.
    ///
    /// Joins the label: secrecy grows (union), integrity degrades
    /// (intersection).
    pub fn observe(&mut self, data_label: &Label) {
        self.label = self.label.join(data_label);
    }

    /// Attempts to declassify (remove secrecy for) the given
    /// principals.
    ///
    /// # Errors
    ///
    /// Returns [`DeclassifyError`] if any requested principal is not
    /// covered by privilege.  Label is **not modified** on failure.
    pub fn declassify(
        &mut self,
        principals: &BTreeSet<Principal>,
        privilege: &Privilege,
    ) -> Result<(), DeclassifyError> {
        let uncovered = privilege.uncovered_declassify(principals);
        if !uncovered.is_empty() {
            return Err(DeclassifyError { unprivileged: uncovered });
        }
        self.label = self.label.declassify(principals);
        Ok(())
    }

    /// Attempts to endorse (restore integrity for) the given
    /// principals.
    ///
    /// # Errors
    ///
    /// Returns [`EndorseError`] if any requested principal is not
    /// covered by privilege.  Label is **not modified** on failure.
    pub fn endorse(
        &mut self,
        principals: &BTreeSet<Principal>,
        privilege: &Privilege,
    ) -> Result<(), EndorseError> {
        let uncovered = privilege.uncovered_endorse(principals);
        if !uncovered.is_empty() {
            return Err(EndorseError { unprivileged: uncovered });
        }
        self.label = self.label.endorse(principals);
        Ok(())
    }

    /// Returns the current label.
    pub fn current_label(&self) -> &Label {
        &self.label
    }
}

// ── Errors ───────────────────────────────────────────────────────

/// Error returned by [`Label::flows_to`] when the flow is blocked.
#[derive(Debug)]
pub struct FlowError {
    /// Secrecy principals present in source but not target.
    pub excess_secrecy: BTreeSet<Principal>,
    /// Integrity principals required by target but missing from source.
    pub missing_integrity: BTreeSet<Principal>,
}

impl fmt::Display for FlowError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut parts = Vec::new();
        if !self.excess_secrecy.is_empty() {
            let names: Vec<_> = self.excess_secrecy.iter().map(|p| p.name()).collect();
            parts.push(format!("excess secrecy: [{}]", names.join(", ")));
        }
        if !self.missing_integrity.is_empty() {
            let names: Vec<_> = self.missing_integrity.iter().map(|p| p.name()).collect();
            parts.push(format!("missing integrity: [{}]", names.join(", ")));
        }
        write!(f, "{}", parts.join("; "))
    }
}

impl std::error::Error for FlowError {}

/// Error from [`ComputationLabel::declassify`].
#[derive(Debug)]
pub struct DeclassifyError {
    pub unprivileged: BTreeSet<Principal>,
}

impl fmt::Display for DeclassifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let names: Vec<_> = self.unprivileged.iter().map(|p| p.name()).collect();
        write!(f, "missing declassification privilege for: [{}]", names.join(", "))
    }
}

impl std::error::Error for DeclassifyError {}

/// Error from [`ComputationLabel::endorse`].
#[derive(Debug)]
pub struct EndorseError {
    pub unprivileged: BTreeSet<Principal>,
}

impl fmt::Display for EndorseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let names: Vec<_> = self.unprivileged.iter().map(|p| p.name()).collect();
        write!(f, "missing endorsement privilege for: [{}]", names.join(", "))
    }
}

impl std::error::Error for EndorseError {}

// ── Tests ────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // -- Helpers --

    fn p(name: &str) -> Principal {
        Principal::new(name)
    }
    fn ps(names: &[&str]) -> BTreeSet<Principal> {
        names.iter().map(|n| p(n)).collect()
    }

    fn local_repo() -> Label {
        Label::secret([p("local_repo")])
    }
    fn github() -> Label {
        Label::secret([p("github")])
    }
    fn google_calendar() -> Label {
        Label::secret([p("google_calendar")])
    }

    // -- Principal tests --

    #[test]
    fn principal_equality_and_ordering() {
        assert_eq!(p("alice"), p("alice"));
        assert_ne!(p("alice"), p("bob"));
        assert!(p("alice") < p("bob"));
    }

    // -- Label lattice tests --

    #[test]
    fn public_is_bottom() {
        let pub_label = Label::public();
        assert!(pub_label.is_public());
        pub_label.flows_to(&local_repo()).expect("public flows to everything");
        pub_label.flows_to(&github()).expect("public flows to everything");
    }

    #[test]
    fn secret_does_not_flow_to_public() {
        assert!(github().flows_to(&Label::public()).is_err());
    }

    #[test]
    fn independent_secrecy_incomparable() {
        assert!(github().flows_to(&google_calendar()).is_err());
        assert!(google_calendar().flows_to(&github()).is_err());
    }

    #[test]
    fn subset_flows_to_superset() {
        let small = github();
        let big = Label::secret([p("github"), p("local_repo")]);
        small.flows_to(&big).expect("{github} ⊆ {github, local_repo}");
        assert!(big.flows_to(&small).is_err());
    }

    #[test]
    fn join_unions_secrecy() {
        let a = local_repo();
        let b = a.join(&github());
        assert_eq!(b.secrecy, ps(&["github", "local_repo"]));
    }

    #[test]
    fn join_intersects_integrity() {
        let a = Label::trusted([p("alice"), p("bob")]);
        let b = Label::trusted([p("alice")]);
        let joined = a.join(&b);
        assert_eq!(joined.integrity, ps(&["alice"]));
    }

    #[test]
    fn integrity_flows_to_lower() {
        let high = Label::trusted([p("alice"), p("bob")]);
        let low = Label::trusted([p("alice")]);
        high.flows_to(&low).expect("higher integrity flows to lower");
    }

    #[test]
    fn integrity_does_not_flow_to_higher() {
        let low = Label::trusted([p("alice")]);
        let high = Label::trusted([p("alice"), p("bob")]);
        let err = low.flows_to(&high).unwrap_err();
        assert!(err.missing_integrity.contains(&p("bob")));
    }

    #[test]
    fn combined_flow_check() {
        // Data: secret to github, trusted by alice.
        let data = Label::new([p("github")], [p("alice")]);
        // Channel: accepts github secrets, requires alice integrity.
        let channel = Label::new([p("github")], [p("alice")]);
        data.flows_to(&channel).expect("exact match flows");

        // Channel requiring more integrity → blocked.
        let strict = Label::new([p("github")], [p("alice"), p("bob")]);
        assert!(data.flows_to(&strict).is_err());
    }

    // -- Privilege tests --

    #[test]
    fn privilege_covers_declassify() {
        let priv_ = Privilege::for_declassification([p("local_repo")]);
        assert!(priv_.covers_declassify(&ps(&["local_repo"])));
        assert!(!priv_.covers_declassify(&ps(&["github"])));
    }

    #[test]
    fn privilege_covers_endorse() {
        let priv_ = Privilege::for_endorsement([p("alice")]);
        assert!(priv_.covers_endorse(&ps(&["alice"])));
        assert!(!priv_.covers_endorse(&ps(&["bob"])));
    }

    #[test]
    fn privilege_merge() {
        let a = Privilege::for_declassification([p("x")]);
        let b = Privilege::for_endorsement([p("y")]);
        let merged = a.merge(&b);
        assert!(merged.covers_declassify(&ps(&["x"])));
        assert!(merged.covers_endorse(&ps(&["y"])));
    }

    // -- ComputationLabel tests --

    #[test]
    fn untainted_is_public() {
        let pc = ComputationLabel::untainted();
        assert!(pc.current_label().is_public());
    }

    #[test]
    fn observe_taints() {
        let mut pc = ComputationLabel::untainted();
        pc.observe(&github());
        assert!(pc.current_label().flows_to(&Label::public()).is_err());
    }

    #[test]
    fn observe_accumulates_secrecy() {
        let mut pc = ComputationLabel::untainted();
        pc.observe(&local_repo());
        pc.observe(&github());
        assert_eq!(pc.current_label().secrecy, ps(&["github", "local_repo"]));
    }

    #[test]
    fn observe_degrades_integrity() {
        let mut pc = ComputationLabel::new(Label::trusted([p("alice"), p("bob")]));
        pc.observe(&Label::trusted([p("alice")]));
        assert_eq!(pc.current_label().integrity, ps(&["alice"]));
    }

    #[test]
    fn declassify_with_privilege() {
        let priv_ = Privilege::for_declassification([p("local_repo")]);
        let mut pc = ComputationLabel::new(local_repo());
        pc.declassify(&ps(&["local_repo"]), &priv_).expect("should succeed");
        assert!(pc.current_label().is_declassified());
    }

    #[test]
    fn declassify_without_privilege_fails() {
        let priv_ = Privilege::none();
        let mut pc = ComputationLabel::new(github());
        let err = pc.declassify(&ps(&["github"]), &priv_).unwrap_err();
        assert!(err.unprivileged.contains(&p("github")));
        assert!(!pc.current_label().is_declassified(), "label unchanged on failure");
    }

    #[test]
    fn endorse_restores_integrity() {
        let priv_ = Privilege::for_endorsement([p("alice")]);
        let mut pc = ComputationLabel::untainted();
        pc.endorse(&ps(&["alice"]), &priv_).expect("should succeed");
        assert!(pc.current_label().integrity.contains(&p("alice")));
    }

    #[test]
    fn endorse_without_privilege_fails() {
        let priv_ = Privilege::none();
        let mut pc = ComputationLabel::untainted();
        let err = pc.endorse(&ps(&["alice"]), &priv_).unwrap_err();
        assert!(err.unprivileged.contains(&p("alice")));
        assert!(pc.current_label().integrity.is_empty(), "label unchanged on failure");
    }

    // -- Scenario: crate_vendor --

    #[test]
    fn scenario_crate_vendor() {
        let priv_ = Privilege::for_declassification([p("local_repo")]);
        let mut pc = ComputationLabel::new(local_repo());

        pc.observe(&local_repo()); // read Cargo.lock
        assert!(pc.current_label().flows_to(&Label::public()).is_err());

        pc.declassify(&ps(&["local_repo"]), &priv_).expect("privileged");
        pc.current_label().flows_to(&Label::public()).expect("HTTP allowed");
    }

    // -- Scenario: integrity flow --

    #[test]
    fn scenario_integrity_flow() {
        let priv_ = Privilege::new([p("alice")], [p("alice")]);
        let mut pc = ComputationLabel::new(Label::new([p("alice")], [p("alice")]));

        // Read untrusted network data → integrity degrades.
        pc.observe(&Label::public());
        assert!(pc.current_label().integrity.is_empty());

        // Endorse to restore alice's integrity.
        pc.endorse(&ps(&["alice"]), &priv_).expect("endorsed");
        assert!(pc.current_label().integrity.contains(&p("alice")));

        // Declassify alice's data.
        pc.declassify(&ps(&["alice"]), &priv_).expect("declassified");
        assert!(pc.current_label().is_declassified());
    }

    // -- Scenario: multi-principal secret --

    #[test]
    fn scenario_multi_principal_secret() {
        // GitHub API key labeled {tzn, github} — needs both to declassify.
        let api_key = Label::secret([p("tzn"), p("github")]);
        let mut pc = ComputationLabel::untainted();
        pc.observe(&api_key);

        // Module only has tzn privilege → partial declassify.
        let partial = Privilege::for_declassification([p("tzn")]);
        pc.declassify(&ps(&["tzn"]), &partial).expect("partial ok");
        assert!(pc.current_label().flows_to(&Label::public()).is_err(), "github still blocks");

        // Module also gets github privilege → full declassify.
        let full = Privilege::for_declassification([p("github")]);
        pc.declassify(&ps(&["github"]), &full).expect("full ok");
        assert!(pc.current_label().is_declassified());
    }
}
