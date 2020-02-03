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

use std::collections::HashMap;
use std::fs::File;
use std::io::Write;
use std::path::Path;

fn write_files(dir: &Path, files: &HashMap<&str, &str>) {
    for (filename, data) in files.iter() {
        let path = dir.join(filename);
        let mut file = File::create(path).unwrap();
        file.write_all(data.as_bytes()).expect("Write error");
    }
}

fn are_equal_files(files: &Vec<String>, expected_files: &[&str]) -> bool {
    return files.len() == expected_files.len() &&
           files.iter()
                .zip(expected_files.iter())
                .all(|(a, b)| a == b)
}

#[test]
fn get_files_test() {
    let temp_files = hashmap!{
        "1" => "string1",
        "2" => "string2",
        "3" => "string3",
    };

    let temp_dir = tempfile::tempdir().unwrap();
    write_files(temp_dir.path(), &temp_files);

    let files = get_files(temp_dir.path());
    for (filename, data) in temp_files.iter() {
        assert_eq!(
            files.get(&String::from(*filename)),
            Some(&String::from(*data)));
    }
}


#[test]
fn get_changed_and_removed_files_test() {
    let old_files = hashmap!{
        "1" => "string1",
        "2" => "string2",
        "3" => "string3",
    };
    let new_files = hashmap!{
        "1" => "changed_string1",
        "3" => "string3",
        "4" => "string4",
    };
    let expected_changed_files: &[&str] = &["1", "4"];
    let expected_removed_files: &[&str] = &["2"];

    let old_temp_dir = tempfile::tempdir().unwrap();
    let new_temp_dir = tempfile::tempdir().unwrap();

    write_files(old_temp_dir.path(), &old_files);
    write_files(new_temp_dir.path(), &new_files);

    let (mut changed_files, mut removed_files) = get_changed_and_removed_files(
        old_temp_dir.path(), new_temp_dir.path());
        
    changed_files.sort();
    assert_eq!(true, are_equal_files(&changed_files, expected_changed_files));
    
    removed_files.sort();
    assert_eq!(true, are_equal_files(&removed_files, expected_removed_files));
}
