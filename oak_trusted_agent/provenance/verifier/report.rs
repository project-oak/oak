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

//! What the verifier found, and how it reads.

use std::{fmt::Display, io::Write, process::ExitCode};

use oak_trusted_agent_provenance_common::statement::{InTotoStatement, Predicate};
use serde_json::Value;

use crate::workload::Workload;

/// One check and, if it failed, what was found instead.
struct Check {
    description: String,
    failure: Option<String>,
}

impl Check {
    fn new(description: &str, outcome: Result<(), impl Display>) -> Self {
        Self {
            description: description.to_string(),
            failure: outcome.err().map(|error| format!("{error:#}")),
        }
    }

    fn write(&self, w: &mut impl Write) -> std::io::Result<()> {
        match &self.failure {
            None => writeln!(w, "  ✅ {}", self.description),
            Some(found) => writeln!(w, "  ❌ {}: {found}", self.description),
        }
    }
}

/// What the verifier found.
///
/// Outcomes are collected as data and rendered once at the end, so a check
/// that bails cannot leave half-written output behind.
pub struct Report {
    predicate_type: String,
    subjects: Vec<String>,
    predicate: Predicate,
    correctness: Vec<Check>,
    attestation: Vec<Check>,
    workload: Option<Workload>,
}

impl Report {
    pub fn new(statement: &InTotoStatement) -> Self {
        let subjects = statement
            .subject
            .iter()
            .flat_map(|subject| {
                subject
                    .digest
                    .iter()
                    .map(move |(algorithm, hex)| format!("{} ({algorithm}:{hex})", subject.name))
            })
            .collect();
        Self {
            predicate_type: statement.predicate_type.clone(),
            subjects,
            predicate: statement.predicate.clone(),
            correctness: Vec::new(),
            attestation: Vec::new(),
            workload: None,
        }
    }

    /// Records a structural/completeness check (envelope format, statement
    /// schema, subject coverage).
    pub fn check_correctness(&mut self, description: &str, outcome: Result<(), impl Display>) {
        self.correctness.push(Check::new(description, outcome));
    }

    /// Records a cryptographic/attestation check (artifact digest match,
    /// Confidential Space token, workload image identity).
    pub fn check_attestation(&mut self, description: &str, outcome: Result<(), impl Display>) {
        self.attestation.push(Check::new(description, outcome));
    }

    /// Records who produced the artifacts, once a token has vouched for them.
    pub fn attested(&mut self, workload: Workload) {
        self.workload = Some(workload);
    }

    pub fn write(&self, w: &mut impl Write) -> std::io::Result<()> {
        writeln!(w, "📜 Statement")?;
        writeln!(w, "  predicate type  {}", self.predicate_type)?;
        for subject in &self.subjects {
            writeln!(w, "  subject         {subject}")?;
        }

        if !self.predicate.is_empty() {
            writeln!(w, "\n📊 Predicate")?;
            for (key, value) in &self.predicate {
                match value {
                    Value::String(s) => writeln!(w, "  {key:<14}  {s}")?,
                    other => writeln!(w, "  {key:<14}  {other}")?,
                }
            }
        }

        writeln!(w, "\n🔍 Correctness")?;
        for check in &self.correctness {
            check.write(w)?;
        }

        writeln!(w, "\n🔐 Attestation")?;
        for check in &self.attestation {
            check.write(w)?;
        }
        if let Some(workload) = &self.workload {
            writeln!(w, "     ├── image      {}", workload.image_reference.whole())?;
            writeln!(w, "     ├── digest     {}", workload.image_digest)?;
            writeln!(w, "     └── issued at  {}", workload.issued_at)?;
        }

        writeln!(w)?;
        match (self.failed(), &self.workload) {
            (0, Some(_)) => writeln!(w, "✅ VERIFIED")?,
            // Unreachable while the assertion is itself a check, but a missing
            // workload must never read as success.
            (0, None) => writeln!(w, "❌ NOT VERIFIED (no attestation)")?,
            (failed, _) => writeln!(w, "❌ NOT VERIFIED ({failed} check(s) failed)")?,
        }
        Ok(())
    }

    pub fn verdict(&self) -> ExitCode {
        if self.failed() == 0 && self.workload.is_some() {
            ExitCode::SUCCESS
        } else {
            ExitCode::FAILURE
        }
    }

    fn failed(&self) -> usize {
        self.correctness
            .iter()
            .chain(&self.attestation)
            .filter(|check| check.failure.is_some())
            .count()
    }
}

/// Reports a failure that stopped any check running, in the shape of a failed
/// check, so tampering never looks like a crash.
pub fn fatal(error: anyhow::Error) -> ExitCode {
    println!("🔍 Correctness");
    println!("  ❌ {error:#}");
    println!("\n❌ NOT VERIFIED");
    ExitCode::FAILURE
}
