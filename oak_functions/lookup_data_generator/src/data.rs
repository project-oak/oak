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
//

use anyhow::Context;
use bytes::BytesMut;
use location_utils::{find_cell, Cell, IndexKey, IndexValue, Point};
use multimap::MultiMap;
use oak_functions_abi::proto::Entry;
use prost::Message;
use rand::Rng;
use serde::Serialize;

fn create_bytes<R: Rng>(rng: &mut R, size_bytes: usize) -> Vec<u8> {
    let mut buf = vec![0u8; size_bytes];
    rng.fill(buf.as_mut_slice());
    buf
}

fn create_random_entry<R: Rng>(
    rng: &mut R,
    key_size_bytes: usize,
    value_size_bytes: usize,
) -> Entry {
    Entry {
        key: create_bytes(rng, key_size_bytes),
        value: create_bytes(rng, value_size_bytes),
    }
}

/// Generates random lookup entries with the specified sizes for keys and values and serializes it
/// to bytes.
pub fn generate_and_serialize_random_entries<R: Rng>(
    rng: &mut R,
    key_size_bytes: usize,
    value_size_bytes: usize,
    entries: usize,
) -> anyhow::Result<BytesMut> {
    let mut buf = BytesMut::new();
    for _ in 0..entries {
        let entry = create_random_entry(rng, key_size_bytes, value_size_bytes);
        entry
            .encode_length_delimited(&mut buf)
            .context("could not encode entry")?;
    }
    Ok(buf)
}

#[derive(Serialize)]
struct WeatherValue {
    temperature_degrees_celsius: i32,
}

fn create_weather_entry<R: Rng>(rng: &mut R, lat: i32, lon: i32) -> Entry {
    let key = format!("{},{}", lat, lon);
    let value = serde_json::to_string(&create_weather_value(rng)).unwrap();
    Entry {
        key: key.as_bytes().to_vec(),
        value: value.as_bytes().to_vec(),
    }
}

fn create_weather_value<R: Rng>(rng: &mut R) -> WeatherValue {
    let dist = rand::distributions::Uniform::new(-30, 40);
    WeatherValue {
        temperature_degrees_celsius: rng.sample(dist),
    }
}

/// Generates a dense set of random weather lookup entries with one entry for each comibnation of
/// full degree of longitude and latitude.
pub fn generate_and_serialize_weather_entries<R: Rng>(rng: &mut R) -> anyhow::Result<BytesMut> {
    let mut buf = BytesMut::new();
    for lat in -90..=90 {
        for lon in -180..=180 {
            let entry = create_weather_entry(rng, lat, lon);
            entry
                .encode_length_delimited(&mut buf)
                .context("could not encode entry")?;
        }
    }
    Ok(buf)
}

/// Generates a sparse set of random weather lookup entries with a random location for each entry.
pub fn generate_and_serialize_sparse_weather_entries<R: Rng>(
    rng: &mut R,
    entries: usize,
) -> anyhow::Result<BytesMut> {
    let mut buf = BytesMut::new();
    let pi = std::f32::consts::PI;
    // We sample longitude in radians from [-pi, pi).
    let lon_dist = rand::distributions::Uniform::new(-pi, pi);
    // To avoid increased density towards the poles, we sample lattitude in the range [-1, 1] and
    // convert to lattitude using `acos`. See https://mathworld.wolfram.com/SpherePointPicking.html
    let lat_dist = rand::distributions::Uniform::new(-1.0_f32, 1.0);
    let mut keys = vec![];
    let mut cell_map = MultiMap::new();
    for i in 0..entries {
        // Fix the first point to ensure the default example can find at least one data point within
        // 40km.
        let latitude_degrees = if i == 0 {
            52.1_f32
        } else {
            rng.sample(lat_dist).acos().to_degrees()
        };
        let longitude_degrees = if i == 0 {
            0.1_f32
        } else {
            rng.sample(lon_dist).to_degrees()
        };
        let latitude_millidegrees = (latitude_degrees * 1000.0) as i32;
        let longitude_millidegrees = (longitude_degrees * 1000.0) as i32;

        let key = [
            latitude_millidegrees.to_be_bytes(),
            longitude_millidegrees.to_be_bytes(),
        ]
        .concat();
        // Keep index of all keys to support linear scanning.
        keys.push(key.clone());
        // Add cell-based lookup index entries.
        for cell in find_nearby_cells(latitude_degrees, longitude_degrees) {
            let mut value_key = [0; 8];
            value_key.copy_from_slice(&key[0..8]);
            cell_map.insert(
                cell.index.to_bytes(),
                IndexValue {
                    value_key,
                    position: cell.relative_position(latitude_degrees, longitude_degrees),
                }
                .to_bytes(),
            );
        }
        let value = serde_json::to_string(&create_weather_value(rng)).unwrap();
        let entry = Entry {
            key: key.clone(),
            value: value.as_bytes().to_vec(),
        };
        entry
            .encode_length_delimited(&mut buf)
            .context("could not encode entry")?;
    }
    // Add the index entry containin all keys.
    let index = Entry {
        key: "index".as_bytes().to_vec(),
        value: keys.concat(),
    };
    index
        .encode_length_delimited(&mut buf)
        .context("could not encode index")?;
    // Add the cell-based index entries.
    for (key, values) in cell_map.iter_all() {
        let cell_entry = Entry {
            key: key.clone(),
            value: values.concat(),
        };
        cell_entry
            .encode_length_delimited(&mut buf)
            .context("could not encode cell index")?;
    }
    Ok(buf)
}

/// Finds all nearby cells where a point in the cell could be within 40km of the weather data point.
///
/// If the point is above or below the midpoint of the cell we only need to check the row above or
/// below respectively. Similarly, if a point is to the the right or left of the midpoint we only
/// need to check the cell in the same row to the right or left respectively. Note that this
/// assumption does not strictly hold at latitudes above 88° or below -88° but this only affects
/// points within about 200km of the North and South poles.
///
/// Additionally, the longest distance between the midpoint of a cell and its furthest corner is
/// just under 80km. If the cutoff for finding weather data points is 40km, a point in a cell can
/// only fall within this range if the midpoint of the cell is less than 120km from the weather
/// data point.
fn find_nearby_cells(latitude_degrees: f32, longitude_degrees: f32) -> Vec<Cell> {
    let cutoff = 120_000;
    let mut cells = vec![];
    let mid_point = Point { x: 0, y: 0 };
    // Add cells of interest by trying half a degree above and below the point. One of the points
    // will always fall in the current cell and the other will fall above or below depending on
    // whether the point is above or below the midpoint.
    for offset in &[-0.5_f32, 0.5] {
        if let Ok(cell) = find_cell(latitude_degrees + offset, longitude_degrees) {
            let position = cell.relative_position(latitude_degrees, longitude_degrees);
            cells.push(find_row_neighbour(&cell, position.x));
            cells.push(cell);
        }
    }

    // Use only cells within the 120km cutoff.
    cells
        .into_iter()
        .filter(|cell| {
            cell.relative_position(latitude_degrees, longitude_degrees)
                .validate_close_enough(&mid_point, cutoff)
                .is_ok()
        })
        .collect()
}

/// Finds the neighbour in the same row in the same direction as x. If x is zero, it will choose the
/// neighbour to the east.
fn find_row_neighbour(cell: &Cell, x: i32) -> Cell {
    let next_col = if x < 0 {
        cell.index.col - 1
    } else {
        cell.index.col + 1
    };
    Cell {
        width: cell.width,
        col_count: cell.col_count,
        index: IndexKey {
            row: cell.index.row,
            col: (next_col + cell.col_count) % cell.col_count,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use location_utils::IndexKey;

    #[test]
    fn test_find_nearby_cells() {
        // Middle.
        let keys: Vec<IndexKey> = find_nearby_cells(51.5, 0.8)
            .into_iter()
            .map(|cell| cell.index)
            .collect();
        let expected = vec![
            IndexKey { row: 51, col: 1 },
            IndexKey { row: 51, col: 0 },
            IndexKey { row: 52, col: 0 },
        ];
        assert_eq!(keys, expected);

        // Left.
        let keys: Vec<IndexKey> = find_nearby_cells(51.5, 0.001)
            .into_iter()
            .map(|cell| cell.index)
            .collect();
        let expected = vec![IndexKey { row: 51, col: 226 }, IndexKey { row: 51, col: 0 }];
        assert_eq!(keys, expected);

        // Bottom.
        let keys: Vec<IndexKey> = find_nearby_cells(51.01, 0.8)
            .into_iter()
            .map(|cell| cell.index)
            .collect();
        let expected = vec![IndexKey { row: 50, col: 0 }, IndexKey { row: 51, col: 0 }];
        assert_eq!(keys, expected);

        // Top-right.
        let keys: Vec<IndexKey> = find_nearby_cells(51.99, 1.5)
            .into_iter()
            .map(|cell| cell.index)
            .collect();
        let expected = vec![
            IndexKey { row: 51, col: 1 },
            IndexKey { row: 51, col: 0 },
            IndexKey { row: 52, col: 1 },
            IndexKey { row: 52, col: 0 },
        ];
        assert_eq!(keys, expected);
    }
}
