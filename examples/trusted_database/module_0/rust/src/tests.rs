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
        <name>Uninstalled station</name>
        <terminalName>1</terminalName>
        <lat>-10.0</lat>
        <long>-10.0</long>
        <installed>false</installed>
        <locked>false</locked>
        <installDate/>
        <removalDate/>
        <temporary>false</temporary>
        <nbBikes>1</nbBikes>
        <nbEmptyDocks>1</nbEmptyDocks>
        <nbDocks>1</nbDocks>
    </station>
    <station>
        <id>2</id>
        <name>Locked station</name>
        <terminalName>2</terminalName>
        <lat>0.0</lat>
        <long>-10.0</long>
        <installed>true</installed>
        <locked>true</locked>
        <installDate>0</installDate>
        <removalDate/>
        <temporary>false</temporary>
        <nbBikes>1</nbBikes>
        <nbEmptyDocks>1</nbEmptyDocks>
        <nbDocks>1</nbDocks>
    </station>
    <station>
        <id>3</id>
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
        <id>4</id>
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
    let database = parse_database(&XML_DATABASE.as_bytes().to_vec());
    assert_matches!(database, Ok(_));
    assert_eq!(database.unwrap().len(), 4);
}
