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
//! Cleanroom uses a **category-based** confidentiality model inspired
//! by the [Decentralized Label Model (DLM)][dlm]. Each piece of data
//! carries a [`Label`] — a **set of category names** such as
//! `{local_repo}`, `{github}`, or `{google_calendar}`.
//!
//! ## Why categories instead of levels?
//!
//! A linear lattice (Public < Secret < TopSecret) is too coarse: a
//! Google Docs API key and a GitHub token are both "secret," but they
//! represent independent confidentiality concerns. A module trusted
//! to declassify Google Docs data should not automatically be able to
//! declassify GitHub data.
//!
//! With categories, the lattice is the **powerset** of all category
//! names, ordered by subset inclusion:
//!
//! - `{github}` and `{google_calendar}` are **incomparable** — neither is a
//!   subset of the other.
//! - `{github}` ⊂ `{github, google_calendar}` — strictly less confidential.
//! - `∅` (the empty set) is **public** — the bottom of the lattice.
//!
//! ## Lattice operations
//!
//! | Operation | Meaning | Formula |
//! |-----------|---------|---------|
//! | **Join** | Taint acquired by reading | `L₁ ∪ L₂` |
//! | **Flows-to** | Can data flow from here to there? | `L₁ ⊆ L₂` |
//! | **Declassify** | Explicitly release categories | `L \ {categories}` |
//! | **Public** | No restrictions | `∅` |
//!
//! ## Computation label (`pc`)
//!
//! The host tracks a [`ComputationLabel`] per module invocation.  When
//! a module reads a labeled resource (env var, file), `pc` is joined
//! with the resource's label.  Before any **output** operation (HTTP
//! request, stdout to a public channel), the host checks:
//!
//! 1. The module has explicitly called `ifc::declassify` for every category
//!    remaining in `pc`.  (Declassification is deliberate, not automatic — see
//!    [Robust Declassification](#robust-declassification).)
//! 2. Each declassified category is in the module's
//!    [`DeclassificationPrivilege`].
//!
//! ## Robust declassification
//!
//! Naïve declassification is dangerous: if a module processes both a
//! secret and attacker-controlled input, the attacker can steer *what*
//! gets declassified.  [Zdancewic & Myers (2001)][robust] showed that
//! declassification should only be allowed when the integrity of the
//! computation is high — i.e. the decision of *what to declassify*
//! was not influenced by low-integrity data.
//!
//! The integrity dimension is **deferred** in this initial
//! implementation.  The current design tracks confidentiality
//! categories only.  Integrity (an independent lattice dimension) can
//! be layered on later without changing the [`Label`] type — it would
//! become a second field alongside the category set.
//!
//! [dlm]: https://www.cs.cornell.edu/andru/papers/iflow-sosp97/
//! [robust]: https://www.cis.upenn.edu/~stevez/papers/ZM01b.pdf

use std::{collections::BTreeSet, fmt};

use serde::{Deserialize, Serialize};

// ── Label ────────────────────────────────────────────────────────

/// A confidentiality label: a set of category names.
///
/// The lattice is the powerset of all category names, ordered by
/// subset inclusion.  ⊥ (bottom) is the empty set — public data.
///
/// # Examples
///
/// ```
/// # use cleanroom::ifc::Label;
/// let public = Label::public();
/// let github = Label::category("github");
/// let both = Label::categories(["github", "local_repo"]);
///
/// assert!(public.flows_to(&github).is_ok()); // public ⊆ {github}
/// assert!(github.flows_to(&public).is_err()); // {github} ⊄ ∅
/// assert!(github.flows_to(&both).is_ok()); // {github} ⊆ {github, local_repo}
/// ```
#[derive(Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Label(BTreeSet<String>);

impl Label {
    /// The public (bottom) label: no confidentiality restrictions.
    pub fn public() -> Self {
        Self(BTreeSet::new())
    }

    /// A label with a single category.
    pub fn category(name: impl Into<String>) -> Self {
        let mut set = BTreeSet::new();
        set.insert(name.into());
        Self(set)
    }

    /// A label with multiple categories.
    pub fn categories(names: impl IntoIterator<Item = impl Into<String>>) -> Self {
        Self(names.into_iter().map(Into::into).collect())
    }

    /// Returns the join (set union) of two labels.
    ///
    /// This is the taint operation: the result contains all categories
    /// from both labels.
    pub fn join(&self, other: &Label) -> Label {
        Label(self.0.union(&other.0).cloned().collect())
    }

    /// Returns a new label with the given categories removed.
    ///
    /// This is the declassification primitive.  **The caller must
    /// verify privilege** before calling — see
    /// [`ComputationLabel::declassify`].
    fn declassify(&self, categories: &[String]) -> Label {
        Label(self.0.iter().filter(|c| !categories.contains(c)).cloned().collect())
    }

    /// Checks whether data at this label can flow to a channel with
    /// `target` label (i.e. `self ⊆ target`).
    ///
    /// Returns `Ok(())` on success.  On failure, the error carries the
    /// excess categories that block the flow.
    pub fn flows_to(&self, target: &Label) -> Result<(), ExcessCategories> {
        let excess: BTreeSet<String> = self.0.difference(&target.0).cloned().collect();
        if excess.is_empty() { Ok(()) } else { Err(ExcessCategories(excess)) }
    }

    /// Returns `true` if this is the public (empty) label.
    pub fn is_public(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns the category names in this label.
    pub fn category_names(&self) -> &BTreeSet<String> {
        &self.0
    }

    /// Returns the number of categories.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if the label has no categories (synonym for
    /// [`is_public`](Self::is_public)).
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl fmt::Debug for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            write!(f, "Label(∅)")
        } else {
            let cats: Vec<_> = self.0.iter().collect();
            write!(
                f,
                "Label({{{}}})",
                cats.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(", ")
            )
        }
    }
}

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            write!(f, "∅ (public)")
        } else {
            let cats: Vec<_> = self.0.iter().collect();
            write!(f, "{{{}}}", cats.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(", "))
        }
    }
}

// ── DeclassificationPrivilege ────────────────────────────────────

/// The set of categories a module is allowed to declassify.
///
/// This is a **newtype** around `BTreeSet<String>` to distinguish it
/// from a [`Label`] at the type level.  A `Label` is *data about
/// taint*; a `DeclassificationPrivilege` is *authority granted by
/// policy*.  Conflating the two would be a security-relevant type
/// error.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DeclassificationPrivilege(BTreeSet<String>);

impl DeclassificationPrivilege {
    /// No declassification privilege (empty set).
    pub fn none() -> Self {
        Self(BTreeSet::new())
    }

    /// Privilege to declassify the given categories.
    pub fn for_categories(categories: impl IntoIterator<Item = impl Into<String>>) -> Self {
        Self(categories.into_iter().map(Into::into).collect())
    }

    /// Returns `true` if every category in `requested` is covered by
    /// this privilege.
    pub fn covers(&self, requested: &[String]) -> bool {
        requested.iter().all(|c| self.0.contains(c.as_str()))
    }

    /// Returns the categories that are requested but not covered.
    pub fn uncovered(&self, requested: &[String]) -> Vec<String> {
        requested.iter().filter(|c| !self.0.contains(c.as_str())).cloned().collect()
    }

    /// Returns the underlying set.
    pub fn as_set(&self) -> &BTreeSet<String> {
        &self.0
    }
}

// ── ComputationLabel ─────────────────────────────────────────────

/// Tracks the current confidentiality taint for a single module
/// invocation.
///
/// Created at the start of each invocation (typically with
/// `{local_repo}` since stdin comes from within the workspace).
/// Updated whenever the module reads a labeled resource.
///
/// # Invariant
///
/// The set of categories in `pc` only grows via [`observe`](Self::observe)
/// and shrinks via [`declassify`](Self::declassify).  It never grows
/// without an explicit read of a labeled resource.
pub struct ComputationLabel {
    /// The current program-counter label.
    pc: Label,
}

impl ComputationLabel {
    /// Creates a new computation label with the given initial taint.
    ///
    /// # Why start with taint?
    ///
    /// In the cleanroom architecture, stdin comes from a human or
    /// agent working inside the workspace.  Even the *choice* of what
    /// to send to a module may leak information about the repo
    /// contents.  So stdin is conservatively labeled `{local_repo}`.
    pub fn new(initial: Label) -> Self {
        Self { pc: initial }
    }

    /// Creates an untainted (public) computation label.
    pub fn untainted() -> Self {
        Self { pc: Label::public() }
    }

    /// Records that the module observed data with the given label.
    ///
    /// Joins the label into `pc`, raising the taint level.  This is
    /// called by the host when the module reads an env var or file.
    pub fn observe(&mut self, label: &Label) {
        self.pc = self.pc.join(label);
    }

    /// Attempts to declassify the given categories.
    ///
    /// This models the module calling `ifc::declassify(categories)`.
    ///
    /// # Errors
    ///
    /// Returns [`DeclassifyError`] if any requested category is not
    /// covered by [privilege](DeclassificationPrivilege).  In that
    /// case, `pc` is **not modified** — declassification is atomic.
    pub fn declassify(
        &mut self,
        categories: &[String],
        privilege: &DeclassificationPrivilege,
    ) -> Result<(), DeclassifyError> {
        let uncovered = privilege.uncovered(categories);
        if !uncovered.is_empty() {
            return Err(DeclassifyError { unprivileged_categories: uncovered });
        }
        self.pc = self.pc.declassify(categories);
        Ok(())
    }

    /// Returns a snapshot of the current computation label.
    pub fn current_label(&self) -> &Label {
        &self.pc
    }
}

// ── Errors ───────────────────────────────────────────────────────

/// Error returned when a module attempts to declassify categories it
/// does not have privilege for.
#[derive(Debug)]
pub struct DeclassifyError {
    /// Categories the module attempted to declassify but lacks
    /// privilege for.
    pub unprivileged_categories: Vec<String>,
}

impl fmt::Display for DeclassifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "missing declassification privilege for: [{}]",
            self.unprivileged_categories.join(", ")
        )
    }
}

impl std::error::Error for DeclassifyError {}

/// Error returned by [`Label::flows_to`] when the source label
/// contains categories not present in the target channel label.
#[derive(Debug)]
pub struct ExcessCategories(pub BTreeSet<String>);

impl fmt::Display for ExcessCategories {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let cats: Vec<_> = self.0.iter().collect();
        write!(
            f,
            "excess categories: [{}]",
            cats.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(", ")
        )
    }
}

impl std::error::Error for ExcessCategories {}

// ── Tests ────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // -- Label construction helpers --

    fn public() -> Label {
        Label::public()
    }
    fn local_repo() -> Label {
        Label::category("local_repo")
    }
    fn github() -> Label {
        Label::category("github")
    }
    fn google_calendar() -> Label {
        Label::category("google_calendar")
    }

    // -- Label lattice tests --

    #[test]
    fn public_is_bottom_of_the_lattice() {
        let p = public();
        assert!(p.is_public());
        p.flows_to(&local_repo()).expect("public flows to everything");
        p.flows_to(&github()).expect("public flows to everything");
        p.flows_to(&public()).expect("public flows to itself");
    }

    #[test]
    fn single_category_does_not_flow_to_public() {
        assert!(github().flows_to(&public()).is_err());
    }

    #[test]
    fn independent_categories_are_incomparable() {
        assert!(github().flows_to(&google_calendar()).is_err());
        assert!(google_calendar().flows_to(&github()).is_err());
    }

    #[test]
    fn subset_flows_to_superset() {
        let small = github();
        let big = Label::categories(["github", "local_repo"]);

        small.flows_to(&big).expect("{github} ⊆ {github, local_repo}");
        assert!(big.flows_to(&small).is_err(), "{{github, local_repo}} ⊄ {{github}}");
    }

    #[test]
    fn join_is_set_union() {
        let a = local_repo();
        let b = a.join(&github());
        assert_eq!(b, Label::categories(["github", "local_repo"]));
    }

    #[test]
    fn join_is_idempotent() {
        let a = local_repo();
        let b = a.join(&local_repo());
        assert_eq!(b, local_repo());
    }

    #[test]
    fn join_does_not_mutate_originals() {
        let a = local_repo();
        let b = github();
        let c = a.join(&b);

        assert_eq!(a, local_repo(), "original unchanged");
        assert_eq!(b, github(), "original unchanged");
        assert_eq!(c, Label::categories(["github", "local_repo"]));
    }

    // -- DeclassificationPrivilege tests --

    #[test]
    fn privilege_covers_matching_categories() {
        let priv_ = DeclassificationPrivilege::for_categories(["local_repo"]);
        assert!(priv_.covers(&["local_repo".into()]));
    }

    #[test]
    fn privilege_does_not_cover_ungranted_categories() {
        let priv_ = DeclassificationPrivilege::for_categories(["local_repo"]);
        assert!(!priv_.covers(&["github".into()]));
    }

    #[test]
    fn privilege_uncovered_returns_missing_categories() {
        let priv_ = DeclassificationPrivilege::for_categories(["local_repo"]);
        let missing = priv_.uncovered(&["local_repo".into(), "github".into()]);
        assert_eq!(missing, vec!["github"]);
    }

    // -- ComputationLabel tests --

    #[test]
    fn untainted_computation_is_fully_declassified() {
        let pc = ComputationLabel::untainted();
        assert!(pc.current_label().flows_to(&public()).is_ok());
    }

    #[test]
    fn observing_labeled_data_taints_computation() {
        let mut pc = ComputationLabel::untainted();
        pc.observe(&github());

        assert!(pc.current_label().flows_to(&public()).is_err());
        assert_eq!(*pc.current_label(), github());
    }

    #[test]
    fn observing_multiple_resources_accumulates_taint() {
        let mut pc = ComputationLabel::untainted();
        pc.observe(&local_repo());
        pc.observe(&github());

        assert_eq!(
            *pc.current_label(),
            Label::categories(["github", "local_repo"]),
            "taint is the union of all observed labels"
        );
    }

    #[test]
    fn declassify_with_privilege_succeeds() {
        let priv_ = DeclassificationPrivilege::for_categories(["local_repo"]);
        let mut pc = ComputationLabel::new(local_repo());

        pc.declassify(&["local_repo".into()], &priv_).expect("should succeed");
        assert!(pc.current_label().is_public());
    }

    #[test]
    fn declassify_without_privilege_fails_and_preserves_pc() {
        let priv_ = DeclassificationPrivilege::none();
        let mut pc = ComputationLabel::new(github());

        let err = pc.declassify(&["github".into()], &priv_).unwrap_err();
        assert_eq!(err.unprivileged_categories, vec!["github"]);
        assert!(!pc.current_label().is_public(), "pc must not change on failed declassification");
    }

    #[test]
    fn partial_declassify_leaves_remaining_taint() {
        let priv_ = DeclassificationPrivilege::for_categories(["local_repo"]);
        let mut pc = ComputationLabel::new(Label::categories(["local_repo", "github"]));

        pc.declassify(&["local_repo".into()], &priv_).expect("should succeed");
        assert_eq!(*pc.current_label(), github(), "only the declassified category is removed");
    }

    // -- Output channel checks --

    #[test]
    fn public_computation_can_output_to_http() {
        let pc = ComputationLabel::untainted();
        let http_channel = Label::public();

        pc.current_label().flows_to(&http_channel).expect("should be allowed");
    }

    #[test]
    fn tainted_computation_cannot_output_to_http() {
        let pc = ComputationLabel::new(local_repo());
        let http_channel = Label::public();

        assert!(pc.current_label().flows_to(&http_channel).is_err());
    }

    #[test]
    fn tainted_computation_can_output_to_same_level_channel() {
        let pc = ComputationLabel::new(local_repo());
        let agent_channel = local_repo();

        pc.current_label().flows_to(&agent_channel).expect("should be allowed");
    }

    // -- Scenario: crate_vendor module --

    #[test]
    fn scenario_crate_vendor() {
        // crate_vendor reads Cargo.lock (tainted {local_repo}),
        // declassifies, then fetches crates via HTTP (public channel).
        let priv_ = DeclassificationPrivilege::for_categories(["local_repo"]);
        let mut pc = ComputationLabel::new(local_repo()); // stdin is tainted

        // Read Cargo.lock from repo (same label, no change).
        pc.observe(&local_repo());

        // HTTP is blocked before declassification.
        assert!(pc.current_label().flows_to(&public()).is_err(), "must declassify before HTTP");

        // Explicitly declassify.
        pc.declassify(&["local_repo".into()], &priv_).expect("privileged");

        // Now HTTP is allowed.
        pc.current_label().flows_to(&public()).expect("HTTP allowed after declassification");
    }

    // -- Scenario: google_calendar_read module --

    #[test]
    fn scenario_google_calendar_read() {
        // Reads the API key, declassifies, calls Google Calendar API.
        let priv_ = DeclassificationPrivilege::for_categories(["google_calendar"]);
        let mut pc = ComputationLabel::untainted();

        // Read the API key.
        pc.observe(&google_calendar());

        // Declassify and make the HTTP call.
        pc.declassify(&["google_calendar".into()], &priv_).expect("privileged");
        pc.current_label().flows_to(&public()).expect("HTTP allowed");
    }

    // -- Scenario: module reads both GitHub and Google Calendar data
    //    but only has privilege for one --

    #[test]
    fn scenario_insufficient_privilege_blocks_output() {
        let priv_ = DeclassificationPrivilege::for_categories(["github"]);
        let mut pc = ComputationLabel::untainted();

        // Accidentally reads both.
        pc.observe(&github());
        pc.observe(&google_calendar());

        // Can declassify github but not google_calendar.
        pc.declassify(&["github".into()], &priv_).expect("github OK");

        let excess = pc.current_label().flows_to(&public()).unwrap_err();
        assert!(
            excess.0.contains("google_calendar"),
            "google_calendar taint remains and blocks HTTP"
        );
    }
}
