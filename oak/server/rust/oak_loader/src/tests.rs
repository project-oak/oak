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

use crate::options::{parse_config_map, ConfigEntry};
use maplit::hashmap;
use oak_abi::proto::oak::application::ConfigMap;

#[test]
fn parse_config_entry_ok() {
    assert_eq!(
        ConfigEntry {
            key: "foo".to_string(),
            filename: "/dev/null".to_string()
        },
        "foo=/dev/null"
            .parse::<ConfigEntry>()
            .expect("could not parse config entry")
    );
}

#[test]
fn parse_config_entry_multiple_equals_err() {
    assert_eq!(
        false,
        "foo=/dev/null=/foo/bar".parse::<ConfigEntry>().is_ok()
    );
}

#[test]
fn parse_config_entry_missing_equals_err() {
    assert_eq!(false, "/dev/null".parse::<ConfigEntry>().is_ok());
}

#[test]
fn parse_config_map_multiple_ok() {
    let result = parse_config_map(&[
        ConfigEntry {
            key: "foo".to_string(),
            filename: "/dev/null".to_string(),
        },
        ConfigEntry {
            key: "authors".to_string(),
            filename: "../../../../AUTHORS".to_string(),
        },
    ]);
    assert_eq!(
        ConfigMap {
            items: hashmap! {
                "foo".to_string() => vec![],
                "authors".to_string() => b"# This is the list of Project Oak authors for copyright purposes.
#
# This does not necessarily list everyone who has contributed code, since in
# some cases, their employer may be the copyright holder.  To see the full list
# of contributors, see the revision history in source control.
Google LLC
".iter().cloned().collect(),
            },
        },
        result.expect("could not parse config")
    );
}

#[test]
fn parse_config_map_dev_null_ok() {
    let result = parse_config_map(&[ConfigEntry {
        key: "foo".to_string(),
        filename: "/dev/null".to_string(),
    }]);
    assert_eq!(
        ConfigMap {
            items: hashmap! {
                "foo".to_string() => vec![],
            },
        },
        result.expect("could not parse config")
    );
}

#[test]
fn parse_config_map_duplicate_key_err() {
    let result = parse_config_map(&[
        ConfigEntry {
            key: "foo".to_string(),
            filename: "/dev/null".to_string(),
        },
        ConfigEntry {
            key: "foo".to_string(),
            filename: "/dev/null".to_string(),
        },
    ]);
    assert_eq!(false, result.is_ok());
}

#[test]
fn parse_config_map_non_existing_file_err() {
    let result = parse_config_map(&[ConfigEntry {
        key: "foo".to_string(),
        filename: "/non-existing-file".to_string(),
    }]);
    assert_eq!(false, result.is_ok());
}

#[test]
fn parse_config_map_directory_err() {
    let result = parse_config_map(&[ConfigEntry {
        key: "foo".to_string(),
        // Directory.
        filename: "/etc".to_string(),
    }]);
    assert_eq!(false, result.is_ok());
}

#[test]
fn parse_config_map_no_permission_err() {
    let result = parse_config_map(&[ConfigEntry {
        key: "foo".to_string(),
        // File only readable by the root user.
        filename: "/etc/sudoers".to_string(),
    }]);
    assert_eq!(false, result.is_ok());
}
