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

use clap::CommandFactory;
use oak_trusted_agent_eval_common::statement::Predicate;

use super::*;

fn args(subjects: &[&str], waived: &[&str]) -> Args {
    Args {
        statement: PathBuf::new(),
        subjects: subjects.iter().map(|n| (n.to_string(), PathBuf::new())).collect(),
        unchecked_subjects: waived.iter().map(|n| n.to_string()).collect(),
        expected_image_prefix: String::new(),
        expected_image_digest: None,
        expected_predicate_type: None,
        audience: String::new(),
    }
}

/// Catches flag definitions clap rejects at runtime, such as a duplicate long
/// name, which otherwise only surface when someone runs the binary.
#[test]
fn the_command_line_is_well_formed() {
    Args::command().debug_assert();
}

#[test]
fn accounted_covers_both_re_hashed_and_waived_subjects() {
    let args = args(&["report.jsonl"], &["gpt-oss:20b"]);
    assert_eq!(args.accounted().collect::<Vec<_>>(), vec!["report.jsonl", "gpt-oss:20b"]);
}

#[test]
fn require_reports_what_was_found_rather_than_what_was_wanted() {
    assert!(require(true, "ignored").is_ok());
    let error = require(false, "application/json").unwrap_err();
    assert_eq!(format!("{error}"), "application/json");
}

/// Guards the one arm where passing every check could read as VERIFIED for a
/// statement carrying no attestation. Collapsing it into the success arm
/// breaks nothing else.
#[test]
fn a_verdict_without_a_workload_is_never_success() {
    let signed = statement::new(
        vec![statement::subject("report.jsonl", b"passed: 60")],
        "https://example.com/v1".to_string(),
        Predicate::new(),
    )
    .unwrap();

    assert_eq!(Report::new(&signed).verdict(), ExitCode::FAILURE);
}
