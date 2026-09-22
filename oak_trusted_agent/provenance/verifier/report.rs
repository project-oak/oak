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

use oak_trusted_agent_provenance_common::statement::InTotoStatement;

use crate::workload::Workload;

/// One check and, if it failed, what was found instead.
struct Check {
    description: String,
    failure: Option<String>,
}

/// What the verifier found.
///
/// Outcomes are collected as data and rendered once at the end, so a check
/// that bails cannot leave half-written output behind.
pub struct Report {
    predicate_type: String,
    subjects: Vec<String>,
    checks: Vec<Check>,
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
            checks: Vec::new(),
            workload: None,
        }
    }

    /// Records a check rather than short-circuiting, so one failure does not
    /// hide the others.
    pub fn check(&mut self, description: &str, outcome: Result<(), impl Display>) {
        self.checks.push(Check {
            description: description.to_string(),
            failure: outcome.err().map(|error| format!("{error:#}")),
        });
    }

    /// Records who produced the artifacts, once a token has vouched for them.
    pub fn attested(&mut self, workload: Workload) {
        self.workload = Some(workload);
    }

    pub fn write(&self, w: &mut impl Write) -> std::io::Result<()> {
        writeln!(w, "Statement")?;
        writeln!(w, "  predicate type  {}", self.predicate_type)?;
        for subject in &self.subjects {
            writeln!(w, "  subject         {subject}")?;
        }
        writeln!(w, "Checks")?;
        for Check { description, failure } in &self.checks {
            match failure {
                None => writeln!(w, "  ✅ {description}")?,
                Some(found) => writeln!(w, "  ❌ {description}: {found}")?,
            }
        }
        match (self.failed(), &self.workload) {
            (0, Some(workload)) => {
                writeln!(w, "VERIFIED")?;
                writeln!(w, "  produced by  {}", workload.image_reference.whole())?;
                writeln!(w, "  image        {}", workload.image_digest)?;
                writeln!(w, "  attested at  {}", workload.issued_at)?;
            }
            // Unreachable while the assertion is itself a check, but a missing
            // workload must never read as success.
            (0, None) => writeln!(w, "NOT VERIFIED (no attestation)")?,
            (failed, _) => writeln!(w, "NOT VERIFIED ({failed} check(s) failed)")?,
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
        self.checks.iter().filter(|check| check.failure.is_some()).count()
    }
}

/// Reports a failure that stopped any check running, in the shape of a failed
/// check, so tampering never looks like a crash.
pub fn fatal(error: anyhow::Error) -> ExitCode {
    println!("Checks");
    println!("  ❌ {error:#}");
    println!("NOT VERIFIED");
    ExitCode::FAILURE
}
