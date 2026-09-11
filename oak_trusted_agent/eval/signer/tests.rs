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

/// Catches flag definitions clap rejects at runtime, such as a duplicate long
/// name, which otherwise only surface when someone runs the binary.
#[test]
fn the_command_line_is_well_formed() {
    Args::command().debug_assert();
}

#[test]
fn predicate_must_be_a_json_object() {
    let dir = tempfile::tempdir().unwrap();
    let object = dir.path().join("object.json");
    std::fs::write(&object, br#"{"pass_rate": 0.857}"#).unwrap();
    assert_eq!(read_predicate(&object).unwrap()["pass_rate"], 0.857);

    // in-toto allows only an object here, so an array is a mistake worth
    // catching before anything is signed.
    let array = dir.path().join("array.json");
    std::fs::write(&array, b"[1, 2]").unwrap();
    assert!(read_predicate(&array).is_err());
}

#[test]
fn a_missing_predicate_names_the_file() {
    let error = read_predicate(&PathBuf::from("/no/such/predicate.json")).unwrap_err();
    assert!(format!("{error:#}").contains("/no/such/predicate.json"));
}
