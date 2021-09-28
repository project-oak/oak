//
// Copyright 2021 The Project Oak Authors
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

use super::*;

const LONDON_LAT: f64 = 51.5074;
const LONDON_LNG: f64 = -0.1278;

#[test]
fn test_location_from_degrees() {
    let location = location_from_degrees(LONDON_LAT, LONDON_LNG);

    assert_eq!(Into::<E6>::into(&location.lat), E6(51_507_400));
    assert_eq!(Into::<E6>::into(&location.lng), E6(-127_800));
}

#[test]
fn test_location_from_bytes() {
    // Valid bytes.
    let location = location_from_bytes(&[3, 17, 240, 200, 255, 254, 12, 200]).unwrap();

    assert_eq!(Into::<E6>::into(&location.lat), E6(51_507_400));
    assert_eq!(Into::<E6>::into(&location.lng), E6(-127_800));

    // Bytes too short.
    let location_result = location_from_bytes(&[3, 17, 240, 200, 255, 254, 12]);

    assert!(location_result.is_err());

    // Bytes too long.
    let location_result = location_from_bytes(&[3, 17, 240, 200, 255, 254, 12, 200, 0]);

    assert!(location_result.is_err());
}

#[test]
fn test_location_to_bytes() {
    // London.
    let bytes = location_to_bytes(&location_from_degrees(LONDON_LAT, LONDON_LNG));

    assert_eq!(bytes, [3, 17, 240, 200, 255, 254, 12, 200]);

    // Example from readme.
    let bytes = location_to_bytes(&location_from_degrees(14.12_f64, -19.88_f64));

    assert_eq!(bytes, [0x00, 0xD7, 0x74, 0x40, 0xFE, 0xD0, 0xA7, 0xC0]);
}

#[test]
fn test_cell_id_to_bytes() {
    // Find the level 7 s2 cell covering central London.
    // See https://s2.sidewalklabs.com/regioncoverer/?center=51.504569%2C-0.128076&zoom=9&cells=48764
    // for a visualisation.
    let location = location_from_degrees(LONDON_LAT, LONDON_LNG);
    let cell = find_cell(&location, 7).unwrap();

    let bytes = cell_id_to_bytes(&cell);

    assert_eq!(&bytes, b"48764");
}

#[test]
fn test_find_cell() {
    let location = location_from_degrees(LONDON_LAT, LONDON_LNG);
    // Level 2.
    let level = 2;
    let cell = find_cell(&location, level).unwrap();
    let expected = CellID::from(&location).parent(level as u64);

    assert_eq!(cell, expected);

    // Level 7.
    let level = 7;
    let cell = find_cell(&location, level).unwrap();
    let expected = CellID::from(&location).parent(level as u64);

    assert_eq!(cell, expected);

    // Level 20.
    let level = 20;
    let cell = find_cell(&location, level).unwrap();
    let expected = CellID::from(&location).parent(level as u64);

    assert_eq!(cell, expected);

    // Level 30.
    let level = 30;
    let cell = find_cell(&location, level).unwrap();
    let expected = CellID::from(&location);

    assert_eq!(cell.level(), level as u64);
    assert_eq!(cell, expected);

    // Level 31.
    let level = 31;
    let cell = find_cell(&location, level);

    assert!(cell.is_err());
}

#[test]
fn test_find_covering_cells() {
    let location = location_from_degrees(LONDON_LAT, LONDON_LNG);

    // We should only need 2 level-5 cells.
    // See https://s2.sidewalklabs.com/regioncoverer/?center=51.504569%2C-0.128076&zoom=8&cells=47dc,4874
    // for a visualisation.
    let cover =
        find_covering_cells(&location, &Angle::from(DEFAULT_CUTOFF_RADIUS_RADIANS), 5).unwrap();

    assert_eq!(cover.len(), 2);
    assert_eq!(cover[0].to_token(), "47dc");
    assert_eq!(cover[1].to_token(), "4874");

    // We should need 4 level-6 cells.
    // See https://s2.sidewalklabs.com/regioncoverer/?center=51.504569%2C-0.128076&zoom=8&cells=47d9,47df,4875,4877
    // for a visualisation.
    let cover =
        find_covering_cells(&location, &Angle::from(DEFAULT_CUTOFF_RADIUS_RADIANS), 6).unwrap();

    assert_eq!(cover.len(), 4);
    assert_eq!(cover[0].to_token(), "47d9");
    assert_eq!(cover[1].to_token(), "47df");
    assert_eq!(cover[2].to_token(), "4875");
    assert_eq!(cover[3].to_token(), "4877");
}
