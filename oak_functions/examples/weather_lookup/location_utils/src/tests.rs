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

#[test]
fn test_find_cell() {
    // Near equator.
    let equator = find_cell(0.7, -120.3).unwrap().index;
    assert_eq!(equator.row, 0);
    assert_eq!(equator.col, 239);

    // Near 45 degreees.
    let halfway = find_cell(-45.2, 142.5).unwrap().index;
    assert_eq!(halfway.row, -46);
    assert_eq!(halfway.col, 100);

    // Polar circle.
    let polar = find_cell(-89.2, 50.1).unwrap().index;
    assert_eq!(polar.row, -90);
    assert_eq!(polar.col, 0);

    // Invalid values.
    let lat_too_small = find_cell(-90.1, 88.7);
    assert!(lat_too_small.is_err());
    let lat_too_big = find_cell(90.1, 88.7);
    assert!(lat_too_big.is_err());
    let lon_too_small = find_cell(-80.1, -180.7);
    assert!(lon_too_small.is_err());
    let lon_too_big = find_cell(80.1, 180.7);
    assert!(lon_too_big.is_err());
}

#[test]
fn test_final_cell_width() {
    for lat in -90..90 {
        let first_cell = find_cell(lat as f32, 0.0).unwrap();
        let last_cell = find_cell(lat as f32, -1e-9).unwrap();
        // Ensure both cells agree on the number of columns.
        assert_eq!(first_cell.col_count, last_cell.col_count);
        // Ensure that the last cell was really found.
        assert_eq!(last_cell.index.col, last_cell.col_count - 1);
        let actual_last_cell_width = 360.0 - (first_cell.width * last_cell.index.col as f32);
        // Make sure that different between the width of the last cell and widths of the others is
        // within 1%.
        assert!((first_cell.width - actual_last_cell_width).abs() / first_cell.width < 0.01);
    }
}

#[test]
fn test_index_key_round_trip() {
    let initial = IndexKey { row: 30, col: -10 };
    let result = IndexKey::from_bytes(&initial.to_bytes());
    assert_eq!(initial, result);
}

#[test]
fn test_index_value_round_trip() {
    let initial = IndexValue {
        value_key: [8, 7, 6, 5, 4, 3, 2, 1],
        position: Point { x: 99, y: -999 },
    };
    let result = IndexValue::from_bytes(&initial.to_bytes());
    assert_eq!(initial, result);
}

#[test]
fn test_distance_two_points_same_cell() {
    let london_lat = 51.5074;
    let london_lon = 0.1278;
    let chelmsford_lat = 51.7356;
    let chelmsford_lon = 0.4685;

    let cell = find_cell(london_lat, london_lon).unwrap();
    let london = cell.relative_position(london_lat, london_lon);
    let chelmsford = cell.relative_position(chelmsford_lat, chelmsford_lon);

    let distance = (london.squared_distance(&chelmsford) as f32).sqrt() as i32;
    let hav_distance =
        haversine_distance(london_lat, london_lon, chelmsford_lat, chelmsford_lon) as i32;

    // This should be accurate to within im at this scale.
    assert!((distance - hav_distance).abs() <= 1);
}

#[test]
fn test_distance_two_points_different_cell() {
    let london_lat = 51.5074;
    let london_lon = 0.1278;
    let oxford_lat = 51.7520;
    let oxford_lon = -1.2577;

    let hav_distance = haversine_distance(london_lat, london_lon, oxford_lat, oxford_lon) as i32;

    // Check relative to the London cell.
    let cell = find_cell(london_lat, london_lon).unwrap();
    let london = cell.relative_position(london_lat, london_lon);
    let oxford = cell.relative_position(oxford_lat, oxford_lon);

    let distance = (london.squared_distance(&oxford) as f32).sqrt() as i32;

    println!("Cell: {:?}, distance: {}m", cell, distance);
    // Allow up to 10m distortion from the projection at this distance.
    assert!((distance - hav_distance).abs() <= 10);

    // Check relative to the Oxford cell.
    let cell = find_cell(oxford_lat, oxford_lon).unwrap();
    let london = cell.relative_position(london_lat, london_lon);
    let oxford = cell.relative_position(oxford_lat, oxford_lon);

    let distance = (london.squared_distance(&oxford) as f32).sqrt() as i32;

    println!("Cell: {:?}, distance: {}m", cell, distance);
    // Allow up to 10m distortion from the projection at this distance.
    assert!((distance - hav_distance).abs() <= 10);
}

/// Calculates the distance between two points on a spherical approximation of the earth using the
/// Haversine formula.
///
/// See https://en.wikipedia.org/wiki/Haversine_formula
fn haversine_distance(lat1: f32, lon1: f32, lat2: f32, lon2: f32) -> f32 {
    let earth_radius = 6_371_000.0; // Average radius in meters.
    let lat1_radians = lat1.to_radians();
    let lat2_radians = lat2.to_radians();
    let h = haversine(lat2_radians - lat1_radians)
        + lat1_radians.cos()
            * lat2_radians.cos()
            * haversine(lon2.to_radians() - lon1.to_radians());
    2.0 * earth_radius * h.sqrt().atan()
}

fn haversine(theta: f32) -> f32 {
    (theta / 2.0).sin() * (theta / 2.0).sin()
}
