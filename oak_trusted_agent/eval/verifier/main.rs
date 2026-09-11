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

//! Checks a signed statement, without needing a TEE or the artifacts' producer.

use std::{fs, io, path::PathBuf, process::ExitCode};

use anyhow::{Context, Result, anyhow};
use clap::Parser;
use oak_trusted_agent_eval_common::{
    AUDIENCE,
    envelope::{Envelope, PAYLOAD_TYPE},
    flags, statement,
};

use crate::{report::Report, workload::Workload};

mod report;
mod workload;

#[cfg(test)]
mod tests;

#[derive(Parser)]
#[command(about = "Checks a statement signed inside Confidential Space")]
struct Args {
    /// The signed statement to check.
    #[arg(long, value_parser = flags::parse_path)]
    statement: PathBuf,

    /// Artifact to re-hash and compare, as `name=path` or `path`. Repeatable.
    #[arg(long = "subject", value_parser = flags::parse_named_path)]
    subjects: Vec<(String, PathBuf)>,

    /// Subject that cannot be re-hashed here, such as a model known only by
    /// digest. Repeatable. Without this, unchecked subjects fail the run.
    #[arg(long = "unchecked-subject")]
    unchecked_subjects: Vec<String>,

    /// Accept any workload image published under this registry path.
    #[arg(long)]
    expected_image_prefix: String,

    /// Additionally require this exact image digest, as `sha256:…`.
    #[arg(long)]
    expected_image_digest: Option<String>,

    /// Reject the statement unless it carries this predicate type.
    #[arg(long)]
    expected_predicate_type: Option<String>,

    #[arg(long, default_value = AUDIENCE)]
    audience: String,
}

impl Args {
    /// Names the caller took responsibility for, by pointing at a file or by
    /// waiving the subject.
    fn accounted(&self) -> impl Iterator<Item = &str> {
        self.subjects
            .iter()
            .map(|(name, _)| name.as_str())
            .chain(self.unchecked_subjects.iter().map(String::as_str))
    }
}

/// Turns a condition into a check outcome, where the failure carries what was
/// actually found rather than restating the condition.
fn require(condition: bool, found: impl AsRef<str>) -> Result<()> {
    if condition { Ok(()) } else { Err(anyhow!("{}", found.as_ref())) }
}

/// Runs every check, then renders the report. Takes `args` by value so the
/// expected values can move into the workload check.
fn verify(args: Args) -> Result<ExitCode> {
    let envelope = Envelope::read(&args.statement)?;
    let (payload, statement) = envelope.decode_payload()?;

    let mut report = Report::new(&statement);
    report.check(
        "the envelope declares the in-toto media type",
        require(envelope.payload_type == PAYLOAD_TYPE, &envelope.payload_type),
    );
    report.check(
        "the payload is an in-toto v1 Statement",
        require(statement._type == statement::IN_TOTO_TYPE, &statement._type),
    );
    if let Some(expected) = &args.expected_predicate_type {
        report.check(
            "the predicate type is the expected one",
            require(statement.predicate_type == *expected, &statement.predicate_type),
        );
    }

    for (name, path) in &args.subjects {
        let outcome = fs::read(path)
            .with_context(|| format!("reading {}", path.display()))
            .and_then(|contents| statement::check_digest(&statement, name, &contents));
        report.check(&format!("{name} matches the digest in the statement"), outcome);
    }
    let unaccounted = statement::unaccounted(&statement, args.accounted());
    report.check(
        "every subject was re-hashed or waived",
        require(unaccounted.is_empty(), format!("not checked: {}", unaccounted.join(", "))),
    );

    let workload = Workload::from_verified_token(
        &envelope,
        &payload,
        args.audience,
        args.expected_image_prefix,
    );
    report.check(
        "a Confidential Space token binds this exact statement",
        workload.as_ref().map(|_| ()),
    );
    if let Ok(workload) = &workload
        && let Some(expected) = &args.expected_image_digest
    {
        report.check(
            "the workload image is the expected one",
            require(workload.image_digest == *expected, &workload.image_digest),
        );
    }
    if let Ok(workload) = workload {
        report.attested(workload);
    }

    report.write(&mut io::stdout().lock())?;
    Ok(report.verdict())
}

fn main() -> ExitCode {
    match verify(Args::parse()) {
        Ok(code) => code,
        Err(error) => report::fatal(error),
    }
}
