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

//! Utilities for finding and comparing longitude- and latitude-based locations using S2 Geometry.
//!
//! See <https://s2geometry.io/> for more information.

pub use anyhow::{Context, Result};
use s2::{
    cap::Cap,
    region::RegionCoverer,
    s1::{Deg, Rad, E6},
};
pub use s2::{cellid::CellID, latlng::LatLng, s1::Angle};

#[cfg(test)]
mod tests;

/// The default level to use for S2 Geometry cells. Higher numbers means smaller cells. At level 7
/// the cells have roughly similar size to a circle with a radius of 40km and there are apporimately
/// 98K of them.
pub const S2_DEFAULT_LEVEL: u8 = 7;

// Radius of the earth in meters.
const EARTH_RADIUS_METERS: f64 = 6_371_000.;

// The default cutoff radius in meters for the lookup area around a point.
const DEFAULT_CUTOFF_RADIUS_METERS: f64 = 40_000.;

// The size in bytes of the integer representation of a latitude or longitude value.
const LAT_LNG_INTEGER_SIZE: usize = std::mem::size_of::<i32>();

// The size in bytes of the serialized representation of a location.
pub const LOCATION_SIZE: usize = LAT_LNG_INTEGER_SIZE * 2;

/// The default cutoff radius in radians.
pub const DEFAULT_CUTOFF_RADIUS_RADIANS: Rad =
    Rad(DEFAULT_CUTOFF_RADIUS_METERS / EARTH_RADIUS_METERS);

/// Converts latitude and longitude values in degrees to a `LatLng` location.
pub fn location_from_degrees(lat_deg: f64, lng_deg: f64) -> LatLng {
    LatLng::new(Deg(lat_deg).into(), Deg(lng_deg).into())
}

/// Finds the set of S2 cells at the required `level` that covers the area around the `location`.
/// The area is a spherical cap with the `location` as the midpoint with the specified `radius`.
///
/// The level determines the size of the cells. We use a single fixed level for the covering (min
/// level = max level). If the level is higher (and therefore the cells smaller) the coverage is
/// usually tighter with less area that falls inside the cells but outside of the target zone. If
/// the level is lower it would usually require fewer cells to cover the zone, but there is usually
/// larger areas that fall outside of the zone.
///
/// See <https://s2geometry.io/devguide/examples/coverings> for more information on coverings.
pub fn find_covering_cells(location: &LatLng, radius: &Angle, level: u8) -> Result<Vec<CellID>> {
    if level > s2::cellid::MAX_LEVEL as u8 {
        anyhow::bail!("level too high");
    }
    let coverer = RegionCoverer {
        min_level: level,
        max_level: level,
        level_mod: 0,
        max_cells: 0,
    };
    let region = Cap::from_center_angle(&location.into(), radius);
    Ok(coverer.covering(&region).0)
}

/// Finds the cell at the given `level` that covers the `location`.
pub fn find_cell(location: &LatLng, level: u8) -> Result<CellID> {
    let level = level as u64;
    if level > s2::cellid::MAX_LEVEL {
        anyhow::bail!("level too high");
    }
    if level == s2::cellid::MAX_LEVEL {
        return Ok(CellID::from(location));
    }

    // Converting a `LatLng` to `CellID` produces a level 30 cell. We need to find the cells
    // ancestor at the required lower level.
    Ok(CellID::from(location).parent(level))
}

/// Converts a `LatLng` location to a byte representation.
///
/// The latitude and longitude for the location are converted microdegrees (`E6`) values. These
/// values are then converted to big endian byte representations of the underlying 32 bit signed
/// integer and concatenated.
pub fn location_to_bytes(location: &LatLng) -> [u8; 8] {
    let lat: E6 = location.lat.into();
    let lng: E6 = location.lng.into();

    let mut bytes = [0u8; LOCATION_SIZE];
    let (first, second) = bytes.split_at_mut(LAT_LNG_INTEGER_SIZE);
    first.copy_from_slice(&lat.0.to_be_bytes());
    second.copy_from_slice(&lng.0.to_be_bytes());

    bytes
}

/// Converts a byte representation of a location into a `LatLng`.
///
/// The first four bytes represent a big endian signed integer of the latitude in microdegrees
/// (`E6`). The next four bytes are a similar representation of the longitude.
pub fn location_from_bytes(bytes: &[u8]) -> Result<LatLng> {
    if bytes.len() != LOCATION_SIZE {
        anyhow::bail!("incorrect data size");
    }

    let mut lat_bytes = [0; LAT_LNG_INTEGER_SIZE];
    lat_bytes.copy_from_slice(&bytes[0..LAT_LNG_INTEGER_SIZE]);
    let mut lng_bytes = [0; LAT_LNG_INTEGER_SIZE];
    lng_bytes.copy_from_slice(&bytes[LAT_LNG_INTEGER_SIZE..LOCATION_SIZE]);

    Ok(LatLng::new(
        E6(i32::from_be_bytes(lat_bytes)).into(),
        E6(i32::from_be_bytes(lng_bytes)).into(),
    ))
}

/// Converts a `CellID` to a byte representation.
///
/// A `CellID` is a wrapper around a `u64`. The `to_token` function generates a hex-encoded string
/// representation of this internal value and truncates trailing 0s. This is then converted to a
/// vector of bytes.
pub fn cell_id_to_bytes(cell: &CellID) -> Vec<u8> {
    cell.to_token().as_bytes().to_vec()
}

/// Converts a byte representation to the `CellID`.
///
/// A `CellID` is a wrapper around a `u64`. The `to_token` function generates a hex-encoded string
/// representation of this internal value and truncates trailing 0s. This is then converted to a
/// vector of bytes.
pub fn cell_id_from_bytes(bytes: &[u8]) -> Result<CellID> {
    let cell_id = CellID::from_token(
        std::str::from_utf8(bytes).context("could not parse cell id bytes to UTF8 string")?,
    );
    Ok(cell_id)
}
