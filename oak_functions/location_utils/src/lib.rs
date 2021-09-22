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

// Radius of the earth in meters.
const EARTH_RADIUS: f32 = 6_371_000.0;
// The height of a row in degrees latitude.
const CELL_HEIGHT: f32 = 1.0;

/// Represents a cell on a sphere.
/// TODO(#2296): Implement a version based on S2 Geometry for benchmark comparison.
#[derive(Debug, PartialEq)]
pub struct Cell {
    /// The cell width in degrees for a typical cell in this row.
    pub width: f32,
    /// The number of columns in this row. We store this value so that we can easily determine
    /// whether a cell is the last cell for a specific row so that we can adjust the width when
    /// determining the midpoint.
    pub col_count: i16,
    /// The unique identifier of the cell.
    pub index: IndexKey,
}

impl Cell {
    /// Calculates an approximate local cartesian coordinate relative to the location in meters. The
    /// middle of the cell is used as the origin and the y-axis points due North. All points on the
    /// surface of the sphere are projected onto a tangent plane at the midpoint using lines
    /// perpendicular to the plane.
    ///
    /// This approximation is close enough for applications such as finding the closest data
    /// location within a 40km radius of the client as the surface of the earth is very close to
    /// flat at this scale.
    pub fn relative_position(&self, latitude_degrees: f32, longitude_degrees: f32) -> Point {
        // Find the midpoint of the cell.
        let mid_latitude = self.index.row as f32 + CELL_HEIGHT * 0.5;
        let current_width = if self.index.col + 1 == self.col_count {
            360.0 - self.index.col as f32 * self.width
        } else {
            self.width
        };
        let mid_longitude = self.index.col as f32 * self.width + current_width / 2.0;

        // We do the initial projections on a unit sphere and then scale the coordinates by the
        // average radius of the earth in meters.

        let delta_latitude_radians = (latitude_degrees - mid_latitude).to_radians();
        let delta_longitude_radians = (longitude_degrees - mid_longitude).to_radians();

        // If the location and the midpoint had the same longitude the projections of the
        // y-component onto the plane would just be `sin(delta_latitude)`.
        //
        // We need to adjust the y-component to account for the circular nature of the parallel at
        // the location's longitude for the cases where the `delta_latitude != 0`.
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
        let y = ((y_base + offset) * EARTH_RADIUS) as i32;

        // The projection of the x-component onto the plane is given by `sin(delta_longitude)`
        // scaled by cos(latitude) to account for the sphere's curvature.
        let scale = latitude_degrees.to_radians().cos();
        let x = (delta_longitude_radians.sin() * scale * EARTH_RADIUS) as i32;

        Point { x, y }
    }
}

/// An identifier for a cell. The surface of the sphere is covered by cells of approximately the
/// same size.
///
/// Each row lies between two integer degrees of latitude. The row number is the degree of
/// latitude that forms its southern border.
///
/// The rows at the equator are divided into 360 cells. The number of cells in each row above and
/// below is scaled by `cos(latitude_border)` for the border that gives the higer scale value. For
/// the northern hemisphere this is the southern border and vice versa.
///
/// The cell with a western border at 0° longitude has a column number of 0. Column numbers increase
/// eastward and cannot be smaller than 0.
#[derive(Debug, Eq, PartialEq)]
pub struct IndexKey {
    pub row: i16,
    pub col: i16,
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

    /// Converts the `IndexKey` for the cell to bytes. This is used for looking up index entries for
    /// a cell. Locations have 8 byte keys and cells have 4 byte keys, so there is no chance of a
    /// collision.
    pub fn to_bytes(&self) -> Vec<u8> {
        [self.row.to_be_bytes(), self.col.to_be_bytes()].concat()
    }
}

/// Represents an index value for a location-based lookup (e.g weather data).
#[derive(Debug, Eq, PartialEq)]
pub struct IndexValue {
    /// The key for the location's related value (e.g. the current weather at the weather data
    /// location).
    pub value_key: [u8; 8],
    /// The cartesian projection of its position relative to the midpoint of the cell.
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

    /// Calculates the square of the distance between the point and another point.
    ///
    /// The square of the distance is sufficient for finding the minimum, seeing that `sqrt` grows
    /// monotonically.
    pub fn squared_distance(&self, other: &Point) -> i64 {
        ((self.x - other.x) as i64).pow(2) + ((self.y - other.y) as i64).pow(2)
    }

    /// Validates that a point is within a cutoff radius.
    pub fn validate_close_enough(&self, other: &Point, cutoff: i32) -> Result<(), String> {
        let cutoff_sqaured = (cutoff as i64).pow(2);
        if self.squared_distance(other) > cutoff_sqaured {
            return Err(format!("closest data point is more than {}m away", cutoff));
        }
        Ok(())
    }
}

/// Finds the cell in which a location falls.
#[allow(clippy::float_cmp)]
pub fn find_cell(latitude_degrees: f32, longitude_degrees: f32) -> Result<Cell, String> {
    // Validate that the locations is witin the expected bounds.
    if !(-90.0..=90.0).contains(&latitude_degrees) {
        return Err("invalid latitude".to_owned());
    }
    if !(-180.0..=180.0).contains(&longitude_degrees) {
        return Err("invalid longitude".to_owned());
    }

    // Determine which cell the location falls into.
    let south_border = if latitude_degrees == 90.0 {
        90.0 - CELL_HEIGHT
    } else {
        latitude_degrees.floor()
    };
    let north_border = south_border + CELL_HEIGHT;
    // We use the longest border to scale the cell count for the row.
    let ratio = south_border
        .to_radians()
        .cos()
        .max(north_border.to_radians().cos());
    // At the equator there are 360 cells, each with a width of 1°. The number of cells in each row
    // above or below scales with `ratio` to ensure the actual witdhs are roughly similar.
    let cell_count = (360.0 * ratio).ceil();

    let cell_width_degrees = 360.0 / cell_count;

    let row = south_border as i16;
    // We only want positive column numbers, so we wrap negative longitudes around.
    let positive_longitude = if longitude_degrees < 0.0 {
        longitude_degrees + 360.0
    } else {
        longitude_degrees
    };
    let cell_col = (positive_longitude / cell_width_degrees).floor() as i16;

    // Make sure the column does not go out of bounds due to rounding during the division.
    let col = if cell_col >= cell_count as i16 {
        cell_count as i16 - 1
    } else {
        cell_col
    };

    Ok(Cell {
        width: cell_width_degrees,
        col_count: cell_count as i16,
        index: IndexKey { row, col },
    })
}
