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

use std::fs::File;
use std::io::Write;
use std::path::Path;

fn write_files(dir: &Path, filenames: &[&str], data: &[&str]) {
    for (filename, data) in filenames.iter().zip(data.iter()) {
        let path = dir.join(filename);
        let mut file = File::create(path).unwrap();
        file.write_all(data.as_bytes()).expect("Write error");
    }
}

const TEMP_FILES: [&str; 3] = ["1", "2", "3"];

#[test]
fn get_files_test() {
    let temp_dir = tempfile::tempdir().unwrap();
    write_files(temp_dir.path(), &TEMP_FILES, &TEMP_FILES);

    let files = get_files(temp_dir.path());
    for filename_str in TEMP_FILES.iter() {
        let filename = String::from(*filename_str);
        assert_eq!(files.get(&filename), Some(&filename));
    }
}

const OLD_FILES: [&str; 3] = ["1", "2", "3"];
const OLD_FILE_DATA: [&str; 3] = ["1", "2", "3"];
const NEW_FILES: [&str; 4] = ["1", "2", "3", "4"];
const NEW_FILE_DATA: [&str; 4] = ["5", "2", "3", "4"];
const CHANGED_FILES: [&str; 2] = ["1", "4"];

#[test]
fn get_updated_files_test() {
    let old_temp_dir = tempfile::tempdir().unwrap();
    let new_temp_dir = tempfile::tempdir().unwrap();

    write_files(old_temp_dir.path(), &OLD_FILES, &OLD_FILE_DATA);
    write_files(new_temp_dir.path(), &NEW_FILES, &NEW_FILE_DATA);

    let mut updated_files = get_updated_files(old_temp_dir.path(), new_temp_dir.path());
    updated_files.sort();

    assert_eq!(updated_files.len(), CHANGED_FILES.len());
    assert_eq!(
        true,
        updated_files
            .iter()
            .zip(CHANGED_FILES.iter())
            .all(|(a, b)| a == b)
    );
}
