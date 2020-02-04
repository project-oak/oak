//
// Copyright 2020 The Project Oak Authors
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

use crate::*;

use maplit::hashmap;
use std::collections::HashMap;
use std::fs::File;
use std::io::Write;
use std::path::Path;

fn write_files(dir: &Path, files: &HashMap<String, String>) {
    for (filename, data) in files.iter() {
        let path = dir.join(filename);
        let mut file = File::create(path).unwrap();
        file.write_all(data.as_bytes()).expect("Write error");
    }
}

#[test]
fn get_files_test() {
    let temp_files = hashmap!{
        "1".to_string() => "string1".to_string(),
        "2".to_string() => "string2".to_string(),
        "3".to_string() => "string3".to_string(),
    };

    let temp_dir = tempfile::tempdir().unwrap();
    write_files(temp_dir.path(), &temp_files);

    let files = get_files(temp_dir.path());
    assert_eq!(files, temp_files);
}

#[test]
fn filediff_action_test() {
    assert_eq!(
        FileDiff {
            filename: "test".to_string(),
            old_content: Some("1".to_string()),
            new_content: Some("2".to_string()),
        }.action(),
        FileAction::Update {
            new_content: "2".to_string()
        });
    assert_eq!(
        FileDiff {
            filename: "test".to_string(),
            old_content: Some("1".to_string()),
            new_content: Some("1".to_string()),
        }.action(),
        FileAction::Ignore);
    assert_eq!(
        FileDiff {
            filename: "test".to_string(),
            old_content: Some("1".to_string()),
            new_content: None,
        }.action(),
        FileAction::Remove);
    assert_eq!(
        FileDiff {
            filename: "mod.rs".to_string(),
            old_content: Some("1".to_string()),
            new_content: None,
        }.action(),
        FileAction::Ignore);
    assert_eq!(
        FileDiff {
            filename: "test".to_string(),
            old_content: None,
            new_content: Some("2".to_string()),
        }.action(),
        FileAction::Update {
            new_content: "2".to_string()
        });
}

#[test]
fn get_file_diffs_test() {
    let old_files = hashmap!{
        "1".to_string() => "string1".to_string(),
        "2".to_string() => "string2".to_string(),
        "3".to_string() => "string3".to_string(),
    };
    let new_files = hashmap!{
        "1".to_string() => "changed_string1".to_string(),
        "3".to_string() => "string3".to_string(),
        "4".to_string() => "string4".to_string(),
    };
    let mut expected_file_diffs = vec![
        FileDiff {
            filename: "1".to_string(),
            old_content: Some("string1".to_string()),
            new_content: Some("changed_string1".to_string()),
        },
        FileDiff {
            filename: "2".to_string(),
            old_content: Some("string2".to_string()),
            new_content: None,
        },
        FileDiff {
            filename: "3".to_string(),
            old_content: Some("string3".to_string()),
            new_content: Some("string3".to_string()),
        },
        FileDiff {
            filename: "4".to_string(),
            old_content: None,
            new_content: Some("string4".to_string()),
        },
    ];
    expected_file_diffs.sort();

    let mut file_diffs = get_file_diffs(&old_files, &new_files);
    file_diffs.sort();

    assert_eq!(file_diffs, expected_file_diffs);
}

#[test]
fn update_files_test() {
    let old_files = hashmap! {
        "1".to_string() => "string1".to_string(),
        "2".to_string() => "string2".to_string(),
        "3".to_string() => "string3".to_string(),
    };
    let new_files = hashmap! {
        "1".to_string() => "changed_string1".to_string(),
        "3".to_string() => "string3".to_string(),
        "4".to_string() => "string4".to_string(),
    };
    let old_dir = tempfile::tempdir().unwrap();
    let new_dir = tempfile::tempdir().unwrap();
    write_files(old_dir.path(), &old_files);
    write_files(new_dir.path(), &new_files);

    update_files(old_dir.path(), new_dir.path()).expect("Update error");
    let files = get_files(old_dir.path());

    assert_eq!(files, new_files);
}
