//
// Copyright 2023 The Project Oak Authors
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

extern crate alloc;

use alloc::collections::BTreeMap;
use std::{
    fs::{remove_file, File},
    io::{self, Read, Write},
    path::PathBuf,
    process::Command,
};

use anyhow::Result;
use log::warn;
use oak_attestation_verification::claims::{
    ClaimPredicate, Statement, Subject, PREDICATE_V2, STATEMENT_V1,
};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};
use time::OffsetDateTime;

const RESULT_PATH: &str = "result.json";

#[derive(Debug, Deserialize, PartialEq, Serialize)]
pub struct ModelEvaluationSpec {
    script: Subject,
    result: Value,
}

/// Generates a claim in the form of an intoto-statement about the model,
/// identified by the given name and digest, and the given evaluation result.
pub fn generate_claim(
    model_name: &str,
    model_digest: &str,
    script_name: &str,
    script_digest: &str,
    result: &str,
) -> Result<Statement<ClaimPredicate<ModelEvaluationSpec>>> {
    let claim_spec = ModelEvaluationSpec {
        script: Subject {
            name: String::from(script_name),
            digest: BTreeMap::from([(String::from("sha256"), String::from(script_digest))]),
        },
        result: serde_json::from_str(result)?,
    };
    let predicate = ClaimPredicate {
        claim_type: String::from("https://github.com/project-oak/transparent-release/ml-eval/v0"),
        claim_spec: Some(claim_spec),
        usage: "".to_owned(),
        issued_on: OffsetDateTime::now_utc(),
        validity: None,
        evidence: vec![],
    };

    Ok(Statement {
        _type: String::from(STATEMENT_V1),
        predicate_type: String::from(PREDICATE_V2),
        subject: vec![Subject {
            name: String::from(model_name),
            digest: BTreeMap::from([(String::from("sha256"), String::from(model_digest))]),
        }],
        predicate,
    })
}

/// Runs the given evaluation script on the given model, and returns the result
/// as a string, or an error if the evaluation fails.
pub fn run_evaluation(model_path: &PathBuf, eval_path: &PathBuf) -> Result<String> {
    // Run python evaluation script
    let output = Command::new("python3")
        .arg(eval_path)
        .arg("--model")
        .arg(model_path)
        .arg("--output")
        .arg(RESULT_PATH)
        .output()?;

    if !output.status.success() {
        io::stdout().write_all(&output.stdout)?;
        io::stderr().write_all(&output.stderr)?;
        anyhow::bail!("Running the evaluation failed with status {}", output.status,)
    }

    let mut file = File::open(RESULT_PATH)?;
    let mut result = String::new();
    file.read_to_string(&mut result)?;

    // cleanup
    if let Err(e) = remove_file(RESULT_PATH) {
        warn!("could not remove the result file: {e:?}");
    }

    Ok(result)
}

/// Computes a SHA2-256 digest of `input` and returns it as a hex-encoded
/// string.
pub fn get_sha256_hex(input: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(input);
    hex::encode::<[u8; 32]>(hasher.finalize().into())
}

#[cfg(test)]
mod tests {
    use oak_attestation_verification::claims::validate_claim;

    use super::*;

    #[test]
    fn generate_claim_is_valid_json() {
        let claim = generate_claim(
            "mnist",
            "63ea4a9906dbbb3a154f069a0d4bc6a2272b9b8151e69fbd57029c826c2cd779",
            "eval.py",
            "bbfb80f90fb8ebc98f29ccc2a258ba88e712ab0ba754cc1749cb9e8413ac26b0",
            r#"{"acc": "80.9"}"#,
        );
        assert!(claim.is_ok());
        assert!(validate_claim(&claim.unwrap()).is_ok());
    }

    #[test]
    fn get_sha256_hex_hello() {
        let got = get_sha256_hex(b"hello");
        let want = "2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824";
        assert_eq!(want, got);
    }

    #[test]
    fn run_evaluation_returns_result() {
        let script_path = PathBuf::from("testdata/eval.py");
        // This is not really a model, but the evaluation script does not care, and the
        // runner does not care either, as long as it is a file it can load!
        let model_path = PathBuf::from("testdata/eval.py");

        let got = run_evaluation(&script_path, &model_path).expect("running evaluation failed");
        let want = "{\n    \"test_acc\": 80.0\n}";
        assert_eq!(want, got);
    }
}
