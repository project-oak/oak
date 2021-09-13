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

//! Utilities for finding and comparing longitude- and latitude-based locations.

#[cfg(test)]
mod tests;

/// Represents a cell on a sphere.
#[derive(Debug, PartialEq)]
pub struct Cell {
    /// The cell width in degrees.
    pub width: f32,
    /// The unique identifier of the cell.
    pub index: IndexKey,
}

impl Cell {
    /// Calculates an approximate local cartesian coordinate relative of the location in meters. The
    /// middle of the cell is used as the origin and the y-axis points due north. All points on the
    /// surface of the sphere are projected onto a tangent plane at the midpoint using lines
    /// perpendicular to the plane.
    ///
    /// This approximation is close enough for applications such as finding the closest weather
    /// station within a 40km radius of the location as the surface of the earth is very close
    /// to flat at this scale.
    pub fn relative_position(&self, latitude_degrees: f32, longitude_degrees: f32) -> Point {
        // Find the midpoint of the cell.
        let mid_latitude = self.index.row as f32 + 0.5;
        let mid_longitude = self.index.col as f32 * self.width + self.width / 2.0;

        // We do the initial projections on a unit sphere and then scale the coordinates by the
        // average radius of the earth in meters.
        let earth_radius = 6_371_000.0;

        let delta_latitude_radians = (latitude_degrees - mid_latitude).to_radians();
        let delta_longitude_radians = (longitude_degrees - mid_longitude).to_radians();

        // If the location and the midpoint had the same longitude the projections of the
        // y-component onto the plane would just be `sin(delta_latitude)`.
        //
        // We need to adjust the y-component to account for the circular nature of the parallel at
        // the location's longitude for the cases wehre the `delta_latitude != 0`.
        //
        // The radius of the circle formed by the parallel is `cos(latitude)`.
        //
        // The maximal potential effect of the difference in longitude is:
        // `radius * (1 - cos(delta_longitude))`
        //
        // The angle between this circle and a line perpendicular to the plan is `mid_latitude`, so
        // to project the result onto the plane we must scale it by `sin(mid_latitude)`
        let y_base = delta_latitude_radians.sin();
        let offset = (1.0 - delta_longitude_radians.cos())
            * latitude_degrees.to_radians().cos()
            * mid_latitude.to_radians().sin();
        let y = ((y_base + offset) * earth_radius) as i32;

        // The projection of the x-component onto the plane is given by `sin(delta_longitude)`
        // scaled by cos(latitude) to account for the sphere's curvature.
        let scale = latitude_degrees.to_radians().cos();
        let x =
            ((longitude_degrees - mid_longitude).to_radians().sin() * scale * earth_radius) as i32;

        Point { x, y }
    }
}

/// An identifier for a cell. The surface of the sphere is covered by cells of approximately the
/// same size.
///
/// Each row lies between two degrees of latitude. The row number is the degree of
/// latitude that forms its souther border.
///
/// The rows at the equator are divided into 360 cells. The number of cells in each row above and
/// below is scaled by `cos(latitude_border)` for the border that gives the higer scale value.
/// This means the cell width is scaled by `1 / cos(latitude_border)`. For the northern hemisphere
/// this is the southern border and vice versa.
///
/// The cell with a western border at 0° longitude has a
/// column number of 0. Column numbers increase eastward and decrease westward.
#[derive(Debug, Eq, PartialEq)]
pub struct IndexKey {
    row: i16,
    col: i16,
}

impl IndexKey {
    pub fn from_bytes(c: &[u8]) -> IndexKey {
        let mut row_bytes = [0; 2];
        row_bytes.copy_from_slice(&c[0..2]);
        let mut col_bytes = [0; 2];
        col_bytes.copy_from_slice(&c[2..4]);

        IndexKey {
            row: i16::from_be_bytes(row_bytes),
            col: i16::from_be_bytes(col_bytes),
        }
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        [self.row.to_be_bytes(), self.col.to_be_bytes()].concat()
    }
}

/// Represents an index value for a location-based lookup (e.g a weather station). The `value_key`
/// is the key for the location's related value (e.g. the current weather at the weather station)
/// and the `position` is the cartesion projection of its position relative to the midpoint of the
/// cell. Locations have 8 byte keys and cells have 4 byte keys, so there is no chance of a
/// collision.
#[derive(Debug, Eq, PartialEq)]
pub struct IndexValue {
    pub value_key: [u8; 8],
    pub position: Point,
}

impl IndexValue {
    pub fn from_bytes(c: &[u8]) -> IndexValue {
        let mut value_key = [0; 8];
        value_key.copy_from_slice(&c[0..8]);
        IndexValue {
            value_key,
            position: Point::from_bytes(&c[8..16]),
        }
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        [self.value_key[..].to_vec(), self.position.to_bytes()].concat()
    }
}

/// A relative location in cartesian coordinates.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Point {
    /// The relative x-coordinate in meters.
    pub x: i32,
    /// The relative y-coordinate in meters.
    pub y: i32,
}

impl Point {
    pub fn from_bytes(c: &[u8]) -> Point {
        let mut x_bytes = [0; 4];
        x_bytes.copy_from_slice(&c[0..4]);
        let mut y_bytes = [0; 4];
        y_bytes.copy_from_slice(&c[4..8]);

        Point {
            x: i32::from_be_bytes(x_bytes),
            y: i32::from_be_bytes(y_bytes),
        }
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        [self.x.to_be_bytes(), self.y.to_be_bytes()].concat()
    }

    /// Calcluates the square of the distance between the point and another point.
    ///
    /// The square of the distance is sufficient for finding the minimum, seeing that `sqrt` grows
    /// monotonically.
    pub fn squared_distance(&self, other: &Point) -> i64 {
        ((self.x - other.x) as i64).pow(2) + ((self.y - other.y) as i64).pow(2)
    }

    /// Validates that the closest station is no more than 40km away.
    pub fn validate_close_enough(&self, other: &Point, cutoff: i32) -> Result<(), String> {
        let cutoff_sqaured = (cutoff as i64).pow(2);
        if self.squared_distance(other) > cutoff_sqaured {
            return Err(format!(
                "The closest station is more than {}m away.",
                cutoff
            ));
        }
        Ok(())
    }
}

/// Finds the cell in which a location falls.
pub fn find_cell(latitude_degrees: f32, longitude_degrees: f32) -> Result<Cell, String> {
    // Validate that the request is in the expected bounds
    if !(-90.0..=90.0).contains(&latitude_degrees) {
        return Err("invalid latitude".to_owned());
    }
    if !(-180.0..=180.0).contains(&longitude_degrees) {
        return Err("invalid longitude".to_owned());
    }

    // Determine which cell the location falls into.
    let south_border = latitude_degrees.floor();
    let north_border = south_border + 1.0;
    // We use the longest border to scale the cell count for the row.
    let ratio = south_border
        .to_radians()
        .cos()
        .max(north_border.to_radians().cos());
    // At the equator there are 360 cells, each with a width of 1°. The number of cells in each row
    // above or below scales with `ratio` to ensure the actual witdhs are roughly similar. This
    // means that the width in degrees for each cell is `1 / scale`.
    let cell_width_degrees = ratio.recip();
    let cell_row = south_border as i32;
    let cell_col = (longitude_degrees / cell_width_degrees).floor();
    Ok(Cell {
        width: cell_width_degrees,
        index: IndexKey {
            row: cell_row as i16,
            col: cell_col as i16,
        },
    })
}
