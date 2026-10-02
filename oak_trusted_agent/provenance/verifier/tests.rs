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
    let args = args(&["report.jsonl"], &["gemma4:31b-it-qat"]);
    assert_eq!(args.accounted().collect::<Vec<_>>(), vec!["report.jsonl", "gemma4:31b-it-qat"]);
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
    assert_eq!(Report::new().verdict(), ExitCode::FAILURE);
}

#[test]
fn report_renders_attestation_and_omits_passing_correctness_checks() {
    let digest = "sha256:e0812a55773bfeac846b2d605b4d93638b8dfa7119d9587f3d91475afc78185e";
    let mut report = Report::new();
    report.check_correctness("The payload is an in-toto v1 Statement", Ok::<(), &str>(()));
    report.check_attestation(
        "Subject report.jsonl matches the digest in the statement",
        Ok::<(), &str>(()),
    );
    report.attested(Workload {
        issued_at: oak_time::Instant::from_unix_millis(1_700_000_000_000),
        image_reference: format!("example.com/eval/gemma4@{digest}").parse().unwrap(),
        image_digest: digest.to_string(),
    });

    let mut out = Vec::new();
    report.write(&mut out).unwrap();
    let rendered = String::from_utf8(out).unwrap();
    assert!(!rendered.contains("🔍 Correctness"));
    assert!(rendered.contains(&format!("── 🔐 Attestation {}\n  ✅ Subject report.jsonl matches the digest in the statement\n     ├── image      example.com/eval/gemma4\n     ├── digest     {digest}\n", "─".repeat(62))));
    assert!(rendered.ends_with(&format!("\n{}\n✅ VERIFIED\n", "━".repeat(80))));
}
