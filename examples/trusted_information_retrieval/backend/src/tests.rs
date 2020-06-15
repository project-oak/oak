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

use crate::database::parse_database;
use assert_matches::assert_matches;

const XML_DATABASE: &str = r#"<?xml version="1.0" encoding="utf-8"?><stations lastUpdate="1590775020879" version="2.0">
    <station>
        <id>1</id>
        <name>Opened station 1</name>
        <terminalName>3</terminalName>
        <lat>0.0</lat>
        <long>0.0</long>
        <installed>true</installed>
        <locked>false</locked>
        <installDate>0</installDate>
        <removalDate/>
        <temporary>false</temporary>
        <nbBikes>1</nbBikes>
        <nbEmptyDocks>1</nbEmptyDocks>
        <nbDocks>1</nbDocks>
    </station>
    <station>
        <id>2</id>
        <name>Opened station 2</name>
        <terminalName>4</terminalName>
        <lat>10.0</lat>
        <long>0.0</long>
        <installed>true</installed>
        <locked>false</locked>
        <installDate>0</installDate>
        <removalDate/>
        <temporary>false</temporary>
        <nbBikes>1</nbBikes>
        <nbEmptyDocks>1</nbEmptyDocks>
        <nbDocks>1</nbDocks>
    </station>
</stations>"#;

#[test]
fn test_parse_database() {
    let database = parse_database(XML_DATABASE);
    assert_matches!(database, Ok(_));
    let database = database.unwrap();
    assert_eq!(database.len(), 2);
    assert_eq!(database[0].name, "Opened station 1");
    assert_eq!(database[1].locked, false);
    assert_approx_eq(database[1].latitude_degrees, 10.0);
}

fn assert_approx_eq(left: f32, right: f32) {
    if (left - right).abs() > 0.01 {
        panic!("{} is not equal to {}", left, right);
    }
}
