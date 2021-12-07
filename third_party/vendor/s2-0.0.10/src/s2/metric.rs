/*
Copyright 2015 Google Inc. All rights reserved.
Copyright 2017 Jihyun Yu. All rights reserved.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

//! This file implements functions for various S2 measurements.

use libm::{ilogb, ldexp};
use std::f64::consts::{PI, SQRT_2};

use crate::s2::cellid::MAX_LEVEL;

// A metric is a measure for cells. It is used to describe the shape and size
// of cells. They are useful for deciding which cell level to use in order to
// satisfy a given condition (e.g. that cell vertices must be no further than
// "x" apart). You can use the Value(level) method to compute the corresponding
// length or area on the unit sphere for cells at a given level. The minimum
// and maximum bounds are valid for cells at all levels, but they may be
// somewhat conservative for very large cells (e.g. face cells).
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Metric {
    // Dim is either 1 or 2, for a 1D or 2D metric respectively.
    dim: u8,
    // Deriv is the scaling factor for the metric.
    deriv: f64,
}

macro_rules! metric {
    ($name:ident, $dim:expr, $deriv:expr) => {
        pub const $name: Metric = Metric {
            dim: $dim,
            deriv: $deriv,
        };
    };
}

// Defined metrics.
// Of the projection methods defined in C++, Go only supports the quadratic projection.

// Each cell is bounded by four planes passing through its four edges and
// the center of the sphere. These metrics relate to the angle between each
// pair of opposite bounding planes, or equivalently, between the planes
// corresponding to two different s-values or two different t-values.
metric!(MIN_ANGLE_SPANMETRIC, 1, 4.0 / 3.);
metric!(AVG_ANGLE_SPANMETRIC, 1, PI / 2.);
metric!(MAX_ANGLE_SPANMETRIC, 1, 1.704897179199218452);

// The width of geometric figure is defined as the distance between two
// parallel bounding lines in a given direction. For cells, the minimum
// width is always attained between two opposite edges, and the maximum
// width is attained between two opposite vertices. However, for our
// purposes we redefine the width of a cell as the perpendicular distance
// between a pair of opposite edges. A cell therefore has two widths, one
// in each direction. The minimum width according to this definition agrees
// with the classic geometric one, but the maximum width is different. (The
// maximum geometric width corresponds to MAXDiag defined below.)
//
// The average width in both directions for all cells at level k is approximately
// AVG_WIDTHMETRIC.Value(k).
//
// The width is useful for bounding the minimum or maximum distance from a
// point on one edge of a cell to the closest point on the opposite edge.
// For example, this is useful when growing regions by a fixed distance.
metric!(MIN_WIDTHMETRIC, 1, 2. * SQRT_2 / 3.);
metric!(AVG_WIDTHMETRIC, 1, 1.434523672886099389);
metric!(MAX_WIDTHMETRIC, 1, MAX_ANGLE_SPANMETRIC.deriv);

// The edge length metrics can be used to bound the minimum, maximum,
// or average distance from the center of one cell to the center of one of
// its edge neighbors. In particular, it can be used to bound the distance
// between adjacent cell centers along the space-filling Hilbert curve for
// cells at any given level.
metric!(MIN_EDGEMETRIC, 1, 2. * SQRT_2 / 3.);
metric!(AVG_EDGEMETRIC, 1, 1.459213746386106062);
metric!(MAX_EDGEMETRIC, 1, MAX_ANGLE_SPANMETRIC.deriv);

/// MAX_EDGE_ASPECT is the maximum edge aspect ratio over all cells at any level,
/// where the edge aspect ratio of a cell is defined as the ratio of its longest
/// edge length to its shortest edge length.
pub const MAX_EDGE_ASPECT: f64 = 1.442615274452682920;

metric!(MIN_AREAMETRIC, 2, 8. * SQRT_2 / 9.);
metric!(AVG_AREAMETRIC, 2, 4. * PI / 6.);
metric!(MAX_AREAMETRIC, 2, 2.635799256963161491);

// The maximum diagonal is also the maximum diameter of any cell,
// and also the maximum geometric width (see the comment for widths). For
// example, the distance from an arbitrary point to the closest cell center
// at a given level is at most half the maximum diagonal length.
metric!(MIN_DIAGMETRIC, 1, 8. * SQRT_2 / 9.);
metric!(AVG_DIAGMETRIC, 1, 2.060422738998471683);
metric!(MAX_DIAGMETRIC, 1, 2.438654594434021032);

/// MAX_DIAG_ASPECT is the maximum diagonal aspect ratio over all cells at any
/// level, where the diagonal aspect ratio of a cell is defined as the ratio
/// of its longest diagonal length to its shortest diagonal length.
///TODO: 3f64.sqrt()
pub const MAX_DIAG_ASPECT: f64 = 1.7320508075688772;

impl Metric {
    /// value returns the value of the metric at the given level.
    pub fn value(&self, level: u8) -> f64 {
        // return math.Ldexp(m.Deriv, -m.Dim*level)
        ldexp(self.deriv, -1 * (self.dim as i32) * (level as i32))
    }

    /// min_level returns the minimum level such that the metric is at most
    /// the given value, or maxLevel (30) if there is no such level.
    ///
    /// For example, MINLevel(0.1) returns the minimum level such that all cell diagonal
    /// lengths are 0.1 or smaller. The returned value is always a valid level.
    ///
    /// In C++, this is called GetLevelForMAXValue.
    pub fn min_level(&self, val: f64) -> u64 {
        if val < 0. {
            return MAX_LEVEL;
        }

        let level = -ilogb(val / self.deriv) >> u64::from(self.dim - 1);
        if level > (MAX_LEVEL as i32) {
            MAX_LEVEL
        } else if level < 0 {
            0
        } else {
            level as u64
        }
    }

    /// max_level returns the maximum level such that the metric is at least
    /// the given value, or zero if there is no such level.
    ///
    /// For example, MAXLevel(0.1) returns the maximum level such that all cells have a
    /// minimum width of 0.1 or larger. The returned value is always a valid level.
    ///
    /// In C++, this is called GetLevelForMINValue.
    pub fn max_level(&self, val: f64) -> u64 {
        if val <= 0. {
            return MAX_LEVEL;
        }

        let level = ilogb(self.deriv / val) >> u64::from(self.dim - 1);
        if level > (MAX_LEVEL as i32) {
            MAX_LEVEL
        } else if level < 0 {
            0
        } else {
            level as u64
        }
    }

    /// closest_level returns the level at which the metric has approximately the given
    /// value. The return value is always a valid level. For example,
    /// AVG_EDGEMETRIC.closest_level(0.1) returns the level at which the average cell edge
    /// length is approximately 0.1.
    pub fn closest_level(&self, val: f64) -> u64 {
        let x = if self.dim == 2 { 2. } else { SQRT_2 };
        self.min_level(x * val)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore]
    fn test_metric() {
        assert_eq!(9, MIN_WIDTHMETRIC.max_level(0.001256));

        // Check that the maximum aspect ratio of an individual cell is consistent
        // with the global minimums and maximums.
        assert!(MAX_EDGE_ASPECT >= 1.);
        assert!(MAX_EDGEMETRIC.deriv / MIN_EDGEMETRIC.deriv <= MAX_EDGE_ASPECT);

        assert!(MAX_DIAG_ASPECT >= 1.);
        assert!(MAX_DIAGMETRIC.deriv / MIN_DIAGMETRIC.deriv <= MAX_DIAG_ASPECT);

        // Check that area is consistent with edge and width.
        assert!(MIN_WIDTHMETRIC.deriv / MIN_EDGEMETRIC.deriv - 1e-15 <= MIN_AREAMETRIC.deriv);
        assert!(MAX_WIDTHMETRIC.deriv / MAX_EDGEMETRIC.deriv + 1e-15 >= MAX_AREAMETRIC.deriv);
    }
}

/*
package s2

import (
    "math"
    "testing"
)

func TestMetric(t *testing.T) {
    if got := MinWidthMetric.Deriv*MinEdgeMetric.Deriv - 1e-15; MinAreaMetric.Deriv < got {
        t.Errorf("Min Area: %v*%v = %v, want >= %v", MinWidthMetric.Deriv, MinEdgeMetric.Deriv, got, MinAreaMetric.Deriv)
    }
    if got := MaxWidthMetric.Deriv*MaxEdgeMetric.Deriv + 1e-15; MaxAreaMetric.Deriv > got {
        t.Errorf("Max Area: %v*%v = %v, want <= %v", MaxWidthMetric.Deriv, MaxEdgeMetric.Deriv, got, MaxAreaMetric.Deriv)
    }

    for level := -2; level <= maxLevel+3; level++ {
        width := MinWidthMetric.Deriv * math.Pow(2, float64(-level))
        if level >= maxLevel+3 {
            width = 0
        }

        // Check boundary cases (exactly equal to a threshold value).
        expected := int(math.Max(0, math.Min(maxLevel, float64(level))))

        if MinWidthMetric.MinLevel(width) != expected {
            t.Errorf("MinWidthMetric.MinLevel(%v) = %v, want %v", width, MinWidthMetric.MinLevel(width), expected)
        }
        if MinWidthMetric.MaxLevel(width) != expected {
            t.Errorf("MinWidthMetric.MaxLevel(%v) = %v, want %v", width, MinWidthMetric.MaxLevel(width), expected)
        }
        if MinWidthMetric.ClosestLevel(width) != expected {
            t.Errorf("MinWidthMetric.ClosestLevel(%v) = %v, want %v", width, MinWidthMetric.ClosestLevel(width), expected)
        }

        // Also check non-boundary cases.
        if got := MinWidthMetric.MinLevel(1.2 * width); got != expected {
            t.Errorf("non-boundary MinWidthMetric.MinLevel(%v) = %v, want %v", 1.2*width, got, expected)
        }
        if got := MinWidthMetric.MaxLevel(0.8 * width); got != expected {
            t.Errorf("non-boundary MinWidthMetric.MaxLevel(%v) = %v, want %v", 0.8*width, got, expected)
        }
        if got := MinWidthMetric.ClosestLevel(1.2 * width); got != expected {
            t.Errorf("non-boundary larger MinWidthMetric.ClosestLevel(%v) = %v, want %v", 1.2*width, got, expected)
        }
        if got := MinWidthMetric.ClosestLevel(0.8 * width); got != expected {
            t.Errorf("non-boundary smaller MinWidthMetric.ClosestLevel(%v) = %v, want %v", 0.8*width, got, expected)
        }
    }
}

func TestMetricSizeRelations(t *testing.T) {
    // check that min <= avg <= max for each metric.
    tests := []struct {
        min Metric
        avg Metric
        max Metric
    }{
        {MinAngleSpanMetric, AvgAngleSpanMetric, MaxAngleSpanMetric},
        {MinWidthMetric, AvgWidthMetric, MaxWidthMetric},
        {MinEdgeMetric, AvgEdgeMetric, MaxEdgeMetric},
        {MinDiagMetric, AvgDiagMetric, MaxDiagMetric},
        {MinAreaMetric, AvgAreaMetric, MaxAreaMetric},
    }

    for _, test := range tests {
        if test.min.Deriv > test.avg.Deriv {
            t.Errorf("Min %v > Avg %v", test.min.Deriv, test.avg.Deriv)
        }
        if test.avg.Deriv > test.max.Deriv {
            t.Errorf("Avg %v > Max %v", test.avg.Deriv, test.max.Deriv)
        }
    }
}
*/
