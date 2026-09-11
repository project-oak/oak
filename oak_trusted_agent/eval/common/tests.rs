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

use std::sync::Mutex;

use base64::{Engine, engine::general_purpose::STANDARD as BASE64};
use oak_attestation_types::assertion_generator::{AssertionGenerator, AssertionGeneratorError};
use oak_proto_rust::oak::attestation::v1::Assertion;

use crate::{
    envelope::{ASSERTION_ID, Envelope, PAYLOAD_TYPE},
    statement::{self, IN_TOTO_TYPE, InTotoStatement, Predicate},
};

/// Records the bytes it was asked to assert, so tests can check the published
/// payload is the payload that was signed.
#[derive(Default)]
struct RecordingGenerator {
    asserted: Mutex<Vec<u8>>,
}

impl AssertionGenerator for RecordingGenerator {
    fn generate(&self, data: &[u8]) -> Result<Assertion, AssertionGeneratorError> {
        *self.asserted.lock().unwrap() = data.to_vec();
        Ok(Assertion { content: b"token".to_vec() })
    }
}

fn statement_about(contents: &[u8]) -> InTotoStatement {
    statement::new(
        vec![statement::subject("report.jsonl", contents)],
        "https://project-oak.dev/attestation/model-eval/v1".to_string(),
        Predicate::new(),
    )
    .unwrap()
}

fn statement() -> InTotoStatement {
    statement_about(b"hello")
}

mod envelope_tests {
    use std::path::PathBuf;

    use super::*;

    #[test]
    fn the_published_payload_is_the_payload_that_was_signed() {
        let generator = RecordingGenerator::default();
        let signed = Envelope::new(&statement(), Some(&generator)).unwrap();

        let published = BASE64.decode(&signed.payload).unwrap();
        assert_eq!(published, *generator.asserted.lock().unwrap());
        assert_eq!(signed.payload_type, PAYLOAD_TYPE);
        assert!(signed.assertions.contains_key(ASSERTION_ID));
    }

    #[test]
    fn an_envelope_without_a_generator_asserts_nothing() {
        assert!(Envelope::new(&statement(), None).unwrap().assertions.is_empty());
    }

    #[test]
    fn decoding_recovers_the_signed_bytes() {
        let generator = RecordingGenerator::default();
        let signed = Envelope::new(&statement(), Some(&generator)).unwrap();

        let (payload, decoded) = signed.decode_payload().unwrap();
        assert_eq!(payload, *generator.asserted.lock().unwrap());
        assert_eq!(decoded, statement());
        assert_eq!(signed.decode_assertion().unwrap().content, b"token");
    }

    #[test]
    fn an_unsigned_envelope_has_no_assertion_to_decode() {
        assert!(Envelope::new(&statement(), None).unwrap().decode_assertion().is_err());
    }

    #[test]
    fn envelope_round_trips() {
        let signed = Envelope::new(&statement(), Some(&RecordingGenerator::default())).unwrap();
        let json = serde_json::to_vec(&signed).unwrap();
        assert_eq!(serde_json::from_slice::<Envelope>(&json).unwrap(), signed);
        assert!(String::from_utf8(json).unwrap().contains("payloadType"));
    }

    #[test]
    fn payload_changes_when_a_subject_changes() {
        let of = |contents: &[u8]| Envelope::new(&statement_about(contents), None).unwrap().payload;
        assert_ne!(of(b"passed: 60"), of(b"passed: 70"));
    }

    #[test]
    fn what_is_written_is_a_json_document_that_reads_back() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("signed.json");
        let signed = Envelope::new(&statement(), None).unwrap();

        signed.write(&path).unwrap();

        let written = std::fs::read_to_string(&path).unwrap();
        assert!(written.ends_with('\n'), "should be a well-formed text file");
        assert_eq!(Envelope::read(&path).unwrap(), signed);
    }

    #[test]
    fn reading_a_missing_envelope_names_the_file() {
        let error = Envelope::read(&PathBuf::from("/no/such/statement.json")).unwrap_err();
        assert!(format!("{error:#}").contains("/no/such/statement.json"));
    }

    #[test]
    fn reading_a_malformed_envelope_says_so() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("statement.json");
        std::fs::write(&path, b"not json").unwrap();

        let error = Envelope::read(&path).unwrap_err();
        assert!(format!("{error:#}").contains("parsing the envelope"));
    }
}

mod statement_tests {
    use std::path::PathBuf;

    use super::*;
    use crate::flags::parse_named_digest;

    #[test]
    fn serializes_to_the_in_toto_shape() {
        let json: serde_json::Value =
            serde_json::from_slice(&serde_json::to_vec(&statement()).unwrap()).unwrap();
        assert_eq!(json["_type"], IN_TOTO_TYPE);
        assert_eq!(json["predicateType"], "https://project-oak.dev/attestation/model-eval/v1");
        assert_eq!(json["subject"][0]["name"], "report.jsonl");
    }

    #[test]
    fn rejects_what_in_toto_forbids() {
        let subject = || vec![statement::subject("report.jsonl", b"hello")];
        assert!(
            statement::new(vec![], "https://example.com/v1".to_string(), Predicate::new()).is_err()
        );
        assert!(statement::new(subject(), String::new(), Predicate::new()).is_err());
        let mut duplicated = subject();
        duplicated.extend(subject());
        assert!(
            statement::new(duplicated, "https://example.com/v1".to_string(), Predicate::new())
                .is_err()
        );
    }

    #[test]
    fn subject_hashes_contents() {
        let subject = statement::subject("report.jsonl", b"");
        assert_eq!(
            subject.digest["sha256"],
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }

    #[test]
    fn subjects_from_paths_reads_files_and_passes_digests_through() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("report.jsonl");
        std::fs::write(&path, b"passed: 60").unwrap();
        let (_, digest) = parse_named_digest(&format!("m=sha256:{}", "a".repeat(64))).unwrap();

        let subjects = statement::subjects_from_paths(
            &[("report.jsonl".to_string(), path)],
            [("m".to_string(), digest)],
        )
        .unwrap();

        assert_eq!(subjects.len(), 2);
        assert_eq!(subjects[0], statement::subject("report.jsonl", b"passed: 60"));
        assert_eq!(subjects[1].name, "m");
    }

    #[test]
    fn subjects_from_paths_reports_the_file_it_could_not_read() {
        let error = statement::subjects_from_paths(
            &[("gone".to_string(), PathBuf::from("/no/such/file"))],
            [],
        )
        .unwrap_err();
        assert!(format!("{error:#}").contains("/no/such/file"));
    }

    #[test]
    fn check_digest_accepts_only_the_recorded_contents() {
        let statement = statement_about(b"passed: 60");

        assert!(statement::check_digest(&statement, "report.jsonl", b"passed: 60").is_ok());
        assert!(statement::check_digest(&statement, "report.jsonl", b"passed: 70").is_err());
        assert!(statement::check_digest(&statement, "other.jsonl", b"passed: 60").is_err());
    }

    #[test]
    fn check_digest_ignores_algorithms_it_does_not_compute() {
        let mut subject = statement::subject("report.jsonl", b"passed: 60");
        subject.digest.insert("sha512".to_string(), "f00d".to_string());
        let statement =
            statement::new(vec![subject], "https://example.com/v1".to_string(), Predicate::new())
                .unwrap();

        // Safe to ignore: the payload is nonce-bound, so no entry can be added
        // after signing, and a matching SHA-256 already identifies the file.
        assert!(statement::check_digest(&statement, "report.jsonl", b"passed: 60").is_ok());
    }

    #[test]
    fn check_digest_rejects_a_digest_it_cannot_check() {
        let mut subject = statement::subject("report.jsonl", b"passed: 60");
        subject.digest.remove("sha256");
        subject.digest.insert("sha512".to_string(), "f00d".to_string());
        let statement =
            statement::new(vec![subject], "https://example.com/v1".to_string(), Predicate::new())
                .unwrap();

        assert!(statement::check_digest(&statement, "report.jsonl", b"passed: 60").is_err());
    }

    #[test]
    fn unaccounted_names_what_nobody_claimed() {
        let statement = statement::new(
            vec![statement::subject("report.jsonl", b"a"), statement::subject("gpt-oss:20b", b"b")],
            "https://example.com/v1".to_string(),
            Predicate::new(),
        )
        .unwrap();

        assert_eq!(statement::unaccounted(&statement, ["report.jsonl"]), vec!["gpt-oss:20b"]);
        assert!(statement::unaccounted(&statement, ["report.jsonl", "gpt-oss:20b"]).is_empty());
    }
}

mod flags_tests {
    use std::path::PathBuf;

    use crate::flags::{parse_named_digest, parse_named_path};

    #[test]
    fn named_path_defaults_to_the_file_name() {
        assert_eq!(
            parse_named_path("/out/report.jsonl").unwrap(),
            ("report.jsonl".to_string(), PathBuf::from("/out/report.jsonl"))
        );
        assert_eq!(
            parse_named_path("garak=/out/report.jsonl").unwrap(),
            ("garak".to_string(), PathBuf::from("/out/report.jsonl"))
        );
    }

    #[test]
    fn named_digest_uses_the_in_toto_spelling() {
        let hex = "a".repeat(64);
        let (name, digest) = parse_named_digest(&format!("gpt-oss:20b=sha256:{hex}")).unwrap();
        assert_eq!(name, "gpt-oss:20b");
        assert_eq!(digest["sha256"], hex);
        // The Oak protos spell it differently, and it is normalized on the way in.
        assert_eq!(parse_named_digest(&format!("m=sha2_256:{hex}")).unwrap().1["sha256"], hex);
    }

    #[test]
    fn named_digest_rejects_what_cannot_be_compared() {
        let hex = "a".repeat(64);
        assert!(parse_named_digest("no-digest").is_err());
        assert!(parse_named_digest("m=sha256:nothex").is_err());
        assert!(parse_named_digest(&format!("=sha256:{hex}")).is_err());
        // Upper case hex is not canonical.
        assert!(parse_named_digest(&format!("m=sha256:{}", "A".repeat(64))).is_err());
        // An algorithm no Oak verifier can evaluate.
        assert!(parse_named_digest(&format!("m=gitCommit:{hex}")).is_err());
    }
}
