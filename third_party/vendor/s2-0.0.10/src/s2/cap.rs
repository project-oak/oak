/*
Copyright 2014 Google Inc. All rights reserved.
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

use std;
use std::f64::consts::PI;

use crate::consts::*;
use crate::r1;
use crate::r3::vector::Vector;
use crate::s1::{self, chordangle, Angle, ChordAngle, Deg, Rad};
use crate::s2::cell::Cell;
use crate::s2::cellid::*;
use crate::s2::edgeutil::*;
use crate::s2::metric::*;
use crate::s2::point::Point;
use crate::s2::rect::Rect;
use crate::s2::region::Region;

const CENTER_POINT: Point = Point(Vector {
    x: 1.,
    y: 0.,
    z: 0.,
});

/// Cap represents a disc-shaped region defined by a center and radius.
/// Technically this shape is called a "spherical cap" (rather than disc)
/// because it is not planar; the cap represents a portion of the sphere that
/// has been cut off by a plane. The boundary of the cap is the circle defined
/// by the intersection of the sphere and the plane. For containment purposes,
/// the cap is a closed set, i.e. it contains its boundary.
///
/// For the most part, you can use a spherical cap wherever you would use a
/// disc in planar geometry. The radius of the cap is measured along the
/// surface of the sphere (rather than the straight-line distance through the
/// interior). Thus a cap of radius π/2 is a hemisphere, and a cap of radius
/// π covers the entire sphere.
///
/// The center is a point on the surface of the unit sphere. (Hence the need for
/// it to be of unit length.)
///
/// A cap can also be defined by its center point and height. The height is the
/// distance from the center point to the cutoff plane. There is also support for
/// "empty" and "full" caps, which contain no points and all points respectively.
///
/// Here are some useful relationships between the cap height (h), the cap
/// radius (r), the maximum chord length from the cap's center (d), and the
/// radius of cap's base (a).
///
/// ```ignore
///     h = 1 - cos(r)
///       = 2 * sin^2(r/2)
///   d^2 = 2 * h
///       = a^2 + h^2
/// ```
///
/// The zero value of Cap is an invalid cap. Use EmptyCap to get a valid empty cap.
#[derive(Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Cap {
    pub center: Point,
    pub radius: ChordAngle,
}

impl std::fmt::Display for Cap {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "[center={:?}, radius={:?}]",
            self.center.0,
            Deg::from(self.radius()).0
        )
    }
}

impl std::fmt::Debug for Cap {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl<'a> From<&'a Point> for Cap {
    /// constructs a cap containing a single point.
    fn from(p: &'a Point) -> Self {
        Cap::from_center_chordangle(p, &ChordAngle(0.))
    }
}

impl Cap {
    /// from_center_angle constructs a cap with the given center and angle.
    pub fn from_center_angle(center: &Point, angle: &Angle) -> Self {
        Cap::from_center_chordangle(center, &ChordAngle::from(angle))
    }

    /// from_center_chordangle constructs a cap where the angle is expressed as an
    /// s1.ChordAngle. This constructor is more efficient than using an s1.Angle.
    pub fn from_center_chordangle(center: &Point, radius: &ChordAngle) -> Self {
        Self {
            center: *center,
            radius: *radius,
        }
    }

    /// from_center_height constructs a cap with the given center and height. A
    /// negative height yields an empty cap; a height of 2 or more yields a full cap.
    /// The center should be unit length.
    pub fn from_center_height(center: &Point, height: f64) -> Self {
        Cap::from_center_chordangle(center, &ChordAngle::from_squared_length(2. * height))
    }

    /// from_center_area constructs a cap with the given center and surface area.
    /// Note that the area can also be interpreted as the solid angle subtended by the
    /// cap (because the sphere has unit radius). A negative area yields an empty cap;
    /// an area of 4*π or more yields a full cap.
    pub fn from_center_area(center: &Point, area: f64) -> Self {
        Cap::from_center_chordangle(center, &ChordAngle::from_squared_length(area / PI))
    }

    /// empty returns a cap that contains no points.
    pub fn empty() -> Cap {
        Cap::from_center_chordangle(&CENTER_POINT, &chordangle::NEGATIVE)
    }

    /// full returns a cap that contains all points.
    pub fn full() -> Cap {
        Cap::from_center_chordangle(&CENTER_POINT, &chordangle::STRAIGHT)
    }

    /// is_valid reports whether the Cap is considered valid.
    pub fn is_valid(&self) -> bool {
        self.center.0.is_unit() && self.radius <= chordangle::STRAIGHT
    }

    /// is_empty reports whether the cap is empty, i.e. it contains no points.
    pub fn is_empty(&self) -> bool {
        self.radius < ChordAngle(0.)
    }

    /// is_full reports whether the cap is empty, i.e. it contains no points.
    pub fn is_full(&self) -> bool {
        self.radius == chordangle::STRAIGHT
    }

    /// center returns the cap's center point.
    pub fn center(&self) -> &Point {
        &self.center
    }

    /// height returns the height of the cap. This is the distance from the center
    /// point to the cutoff plane.
    pub fn height(&self) -> f64 {
        0.5 * self.radius.0
    }

    /// radius returns the cap radius as an Angle. (Note that the cap angle
    /// is stored internally as a ChordAngle, so this method requires a trigonometric
    /// operation and may yield a slightly different result than the value passed
    /// to Cap::from_center_angle).
    pub fn radius(&self) -> Angle {
        Angle::from(&self.radius)
    }

    /// area returns the surface area of the Cap on the unit sphere.
    pub fn area(&self) -> f64 {
        2. * PI * self.height().max(0.)
    }

    /// contains reports whether this cap contains the other.
    pub fn contains(&self, other: &Self) -> bool {
        // In a set containment sense, every cap contains the empty cap.
        if self.is_full() || other.is_empty() {
            true
        } else {
            self.radius >= (&self.center.chordangle(&other.center) + &other.radius)
        }
    }

    /// intersects reports whether this cap intersects the other cap.
    /// i.e. whether they have any points in common.
    pub fn intersects(&self, other: &Self) -> bool {
        if self.is_full() || other.is_empty() {
            false
        } else {
            (&self.radius + &other.radius) >= self.center.chordangle(&other.center)
        }
    }

    /// interior_intersects reports whether this caps interior intersects the other cap.
    pub fn interior_intersects(&self, other: &Self) -> bool {
        // Make sure this cap has an interior and the other cap is non-empty.
        if self.radius.0 <= 0. || other.is_empty() {
            false
        } else {
            (&self.radius + &other.radius) > self.center.chordangle(&other.center)
        }
    }

    /// contains_point reports whether this cap contains the point.
    pub fn contains_point(&self, p: &Point) -> bool {
        self.center.chordangle(p) <= self.radius
    }

    /// interior_contains_point reports whether the point is within the interior of this cap.
    pub fn interior_contains_point(&self, p: &Point) -> bool {
        self.is_full() || self.center.chordangle(p) < self.radius
    }

    /// complement returns the complement of the interior of the cap. A cap and its
    /// complement have the same boundary but do not share any interior points.
    /// The complement operator is not a bijection because the complement of a
    /// singleton cap (containing a single point) is the same as the complement
    /// of an empty cap.
    pub fn complement(&self) -> Cap {
        if self.is_full() {
            Self::empty()
        } else if self.is_empty() {
            Self::full()
        } else {
            Cap::from_center_chordangle(&(self.center * -1.), &(chordangle::STRAIGHT - self.radius))
        }
    }

    /// approx_eq reports whether this cap is equal to the other cap within the given tolerance.
    pub fn approx_eq(&self, other: &Self) -> bool {
        const EPSILON: f64 = 1e-14;
        let r2 = self.radius.0;
        let other_r2 = other.radius.0;
        self.center.approx_eq(&other.center) && (r2 - other_r2).abs() <= EPSILON
            || self.is_empty() && other_r2 <= EPSILON
            || other.is_empty() && r2 <= EPSILON
            || self.is_full() && other_r2 >= 2. - EPSILON
            || other.is_full() && r2 >= 2. - EPSILON
    }

    /// expanded returns a new cap expanded by the given angle. If the cap is empty,
    /// it returns an empty cap.
    pub fn expanded(&self, distance: &Angle) -> Cap {
        if self.is_empty() {
            Self::empty()
        } else {
            Self::from_center_chordangle(
                &self.center,
                &(&self.radius + &ChordAngle::from(distance)),
            )
        }
    }
}

impl Region for Cap {
    /// cap_bound returns a bounding spherical cap. This is not guaranteed to be exact.
    fn cap_bound(&self) -> Cap {
        self.clone()
    }

    /// rect_bound returns a bounding latitude-longitude rectangle.
    /// The bounds are not guaranteed to be tight.
    fn rect_bound(&self) -> Rect {
        if self.is_empty() {
            return Rect::empty();
        }

        let cap_angle = self.radius().rad();
        let mut all_longitudes = false;
        let center_lat = self.center.latitude().rad();
        let mut lat = r1::interval::Interval::new(center_lat - cap_angle, center_lat + cap_angle);
        let mut lng = s1::interval::FULL;

        // Check whether cap includes the south pole.
        if lat.lo < PI / -2. {
            lat.lo = PI / 2.;
            all_longitudes = true;
        }

        // Check whether cap includes the north pole.
        if lat.hi > PI / 2. {
            lat.hi = PI / 2.;
            all_longitudes = true;
        }

        if !all_longitudes {
            // Compute the range of longitudes covered by the cap. We use the law
            // of sines for spherical triangles. Consider the triangle ABC where
            // A is the north pole, B is the center of the cap, and C is the point
            // of tangency between the cap boundary and a line of longitude. Then
            // C is a right angle, and letting a,b,c denote the sides opposite A,B,C,
            // we have sin(a)/sin(A) = sin(c)/sin(C), or sin(A) = sin(a)/sin(c).
            // Here "a" is the cap angle, and "c" is the colatitude (90 degrees
            // minus the latitude). This formula also works for negative latitudes.
            //
            // The formula for sin(a) follows from the relationship h = 1 - cos(a).
            let sin_a = self.radius.0.sin();
            let sin_c = self.center.latitude().rad().cos();
            if sin_a <= sin_c {
                let angle_a = (sin_a / sin_c).asin();
                let center_lng = self.center.longitude().rad();
                lng.lo = remainder(center_lng - angle_a, PI * 2.);
                lng.hi = remainder(center_lng + angle_a, PI * 2.);
            }
        }
        Rect { lat, lng }
    }

    /// contains_cell reports whether the cap contains the given cell.
    fn contains_cell(&self, cell: &Cell) -> bool {
        // If the cap does not contain all cell vertices, return false.
        let vertices = cell.vertices();
        for vert in &vertices {
            if !self.contains_point(vert) {
                return false;
            }
        }
        // Otherwise, return true if the complement of the cap does not intersect the cell.
        !self.complement().intersects_cell_vertices(cell, vertices)
    }

    /// intersects_cell reports whether the cap intersects the cell.
    fn intersects_cell(&self, cell: &Cell) -> bool {
        // If the cap contains any cell vertex, return true.
        let vertices = cell.vertices();
        for vert in &vertices {
            if self.contains_point(vert) {
                return true;
            }
        }
        self.intersects_cell_vertices(cell, vertices)
    }

    /// cell_union_bound computes a covering of the given cap. In general the covering consists of
    /// at most 4 cells (except for very large caps, which may need up to 6 cells).  The output is
    /// not sorted.
    fn cell_union_bound(&self) -> Vec<CellID> {
        let mut v = Vec::new();
        // Find the maximum level such that the cap contains at most one cell vertex
        // and such that CellId.VertexNeighbors() can be called.
        let level = MIN_WIDTHMETRIC.max_level(self.radius().rad());
        if level == 0 {
            for face in 0..6 {
                v.push(CellID::from_face(face));
            }
        } else {
            for ci in CellID::from(&self.center).vertex_neighbors(level - 1) {
                v.push(ci);
            }
        }
        v
    }
}

impl Cap {
    /// intersects_cell_vertices reports whether the cap intersects any point of the cell excluding
    /// its vertices (which are assumed to already have been checked).
    fn intersects_cell_vertices(&self, cell: &Cell, vertices: [Point; 4]) -> bool {
        // If the cap is a hemisphere or larger, the cell and the complement of the cap
        // are both convex. Therefore since no vertex of the cell is contained, no other
        // interior point of the cell is contained either.
        if self.radius >= chordangle::RIGHT {
            return false;
        }

        // We need to check for empty caps due to the center check just below.
        if self.is_empty() {
            return false;
        }

        // Optimization: return true if the cell contains the cap center. This allows half
        // of the edge checks below to be skipped.
        if cell.contains_point(&self.center) {
            return true;
        }

        // At this point we know that the cell does not contain the cap center, and the cap
        // does not contain any cell vertex. The only way that they can intersect is if the
        // cap intersects the interior of some edge.
        let sin2_angle = self.radius.sin2();
        for k in 0..4 {
            let edge = cell.edge(k).0;
            let dot = self.center.0.dot(&edge);
            if dot > 0. {
                // The center is in the interior half-space defined by the edge. We do not need
                // to consider these edges, since if the cap intersects this edge then it also
                // intersects the edge on the opposite side of the cell, because the center is
                // not contained with the cell.
                continue;
            }

            // The Norm2() factor is necessary because "edge" is not normalized.
            if dot * dot > sin2_angle * edge.norm2() {
                return false;
            }

            // Otherwise, the great circle containing this edge intersects the interior of the cap. We just
            // need to check whether the point of closest approach occurs between the two edge endpoints.
            let dir = edge.cross(&self.center.0);
            if dir.dot(&vertices[k].0) < 0. && dir.dot(&vertices[(k + 1) & 3].0) > 0. {
                return true;
            }
        }
        false
    }

    /// Centroid returns the true centroid of the cap multiplied by its surface area
    /// The result lies on the ray from the origin through the cap's center, but it
    /// is not unit length. Note that if you just want the "surface centroid", i.e.
    /// the normalized result, then it is simpler to call Center.
    ///
    /// The reason for multiplying the result by the cap area is to make it
    /// easier to compute the centroid of more complicated shapes. The centroid
    /// of a union of disjoint regions can be computed simply by adding their
    /// Centroid() results. Caveat: for caps that contain a single point
    /// (i.e., zero radius), this method always returns the origin (0, 0, 0).
    /// This is because shapes with no area don't affect the centroid of a
    /// union whose total area is positive.
    pub fn centroid(&self) -> Point {
        // From symmetry, the centroid of the cap must be somewhere on the line
        // from the origin to the center of the cap on the surface of the sphere.
        // When a sphere is divided into slices of constant thickness by a set of
        // parallel planes, all slices have the same surface area. This implies
        // that the radial component of the centroid is simply the midpoint of the
        // range of radial distances spanned by the cap. That is easily computed
        // from the cap height.
        if self.is_empty() {
            Point(Vector {
                x: 0.,
                y: 0.,
                z: 0.,
            })
        } else {
            let r = 1. - 0.5 * self.height();
            Point(self.center.0 * (r * self.area()))
        }
    }

    /// union returns the smallest cap which encloses this cap and other.
    pub fn union(&self, other: &Self) -> Self {
        // If the other cap is larger, swap self and other for the rest of the computations.
        let (a, b) = if self.radius > other.radius {
            (self, other)
        } else {
            (other, self)
        };

        if a.is_full() || b.is_empty() {
            return a.clone();
        }

        // TODO: This calculation would be more efficient using s1.ChordAngles.
        let a_radius = a.radius().rad();
        let b_radius = b.radius().rad();
        let distance = a.center.distance(&b.center).rad();
        if a_radius >= distance + b_radius {
            a.clone()
        } else {
            let res_radius = 0.5 * (distance + a_radius + b_radius);
            let res_center = interpolate_at_distance(
                &Angle::from(Rad(0.5 * (distance - a_radius + b_radius))),
                &self.center,
                &other.center,
            );
            Cap::from_center_chordangle(&res_center, &ChordAngle(res_radius))
        }
    }
}

impl std::cmp::PartialEq for Cap {
    fn eq(&self, other: &Self) -> bool {
        (self.radius == other.radius && self.center == other.center)
            || (self.is_empty() && other.is_empty())
            || (self.is_full() && other.is_full())
    }
}

impl<'a> std::ops::Add<&'a Point> for Cap {
    type Output = Cap;
    /// increases the cap if necessary to include the given point. If this cap is empty,
    /// then the center is set to the point with a zero height. p must be unit-length.
    fn add(self, p: &'a Point) -> Self::Output {
        if self.is_empty() {
            Self::from(p)
        } else {
            // After calling cap.add(p), cap.contains(p) must be true. However
            // we don't need to do anything special to achieve this because Contains()
            // does exactly the same distance calculation that we do here.
            let new_rad = self.center.chordangle(&p).0.max(self.radius.0);
            Self::from_center_chordangle(&self.center, &ChordAngle(new_rad))
        }
    }
}
impl std::ops::Add<Point> for Cap {
    type Output = Cap;
    fn add(self, other: Point) -> Self::Output {
        self + &other
    }
}

impl<'a> std::ops::Add<&'a Cap> for Cap {
    type Output = Cap;
    /// increases the cap height if necessary to include the other cap. If this cap is empty,
    /// it is set to the other cap.
    fn add(self, other: &'a Cap) -> Self::Output {
        if self.is_empty() {
            other.clone()
        } else if other.is_empty() {
            self
        } else {
            // We round up the distance to ensure that the cap is actually contained.
            // TODO(roberts): Do some error analysis in order to guarantee this.
            let dist = &self.center.chordangle(&other.center) + &other.radius;
            let new_rad = dist.expanded(DBL_EPSILON * dist.0).0.max(self.radius.0);
            Self::from_center_chordangle(&self.center, &ChordAngle(new_rad))
        }
    }
}
impl std::ops::Add<Cap> for Cap {
    type Output = Cap;
    fn add(self, other: Cap) -> Self::Output {
        self + &other
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    impl Angle {
        // radius_to_height converts an Angle into the height of the cap.
        pub fn radius_to_height(&self) -> f64 {
            if self.rad() < 0. {
                chordangle::NEGATIVE.0
            } else if self.rad() >= PI {
                chordangle::RIGHT.0
            } else {
                0.5 * ChordAngle::from(self).0
            }
        }
    }
}

/*
package s2

import (
    "math"
    "testing"

    "github.com/golang/geo/r3"
    "github.com/golang/geo/s1"
)

const (
    tinyRad = 1e-10
)

var (
    emptyCap   = EmptyCap()
    fullCap    = FullCap()
    defaultCap = EmptyCap()

    zeroHeight  = 0.0
    fullHeight  = 2.0
    emptyHeight = -1.0

    xAxisPt = Point{r3.Vector{1, 0, 0}}
    yAxisPt = Point{r3.Vector{0, 1, 0}}

    xAxis = CapFromPoint(xAxisPt)
    yAxis = CapFromPoint(yAxisPt)
    xComp = xAxis.Complement()

    hemi    = CapFromCenterHeight(PointFromCoords(1, 0, 1), 1)
    concave = CapFromCenterAngle(PointFromLatLng(LatLngFromDegrees(80, 10)), s1.Angle(150.0)*s1.Degree)
    tiny    = CapFromCenterAngle(PointFromCoords(1, 2, 3), s1.Angle(tinyRad))
)

func TestCapBasicEmptyFullValid(t *testing.T) {
    tests := []struct {
        got                Cap
        empty, full, valid bool
    }{
        {Cap{}, false, false, false},

        {emptyCap, true, false, true},
        {emptyCap.Complement(), false, true, true},
        {fullCap, false, true, true},
        {fullCap.Complement(), true, false, true},
        {defaultCap, true, false, true},

        {xComp, false, true, true},
        {xComp.Complement(), true, false, true},

        {tiny, false, false, true},
        {concave, false, false, true},
        {hemi, false, false, true},
        {tiny, false, false, true},
    }
    for _, test := range tests {
        if e := test.got.IsEmpty(); e != test.empty {
            t.Errorf("%v.IsEmpty() = %t; want %t", test.got, e, test.empty)
        }
        if f := test.got.IsFull(); f != test.full {
            t.Errorf("%v.IsFull() = %t; want %t", test.got, f, test.full)
        }
        if v := test.got.IsValid(); v != test.valid {
            t.Errorf("%v.IsValid() = %t; want %t", test.got, v, test.valid)
        }
    }
}

func TestCapCenterHeightRadius(t *testing.T) {
    if xAxis == xAxis.Complement().Complement() {
        t.Errorf("the complement of the complement is not the original. %v == %v",
            xAxis, xAxis.Complement().Complement())
    }

    if fullCap.Height() != fullHeight {
        t.Error("full Caps should be full height")
    }
    if fullCap.Radius().Degrees() != 180.0 {
        t.Error("radius of x-axis cap should be 180 degrees")
    }

    if emptyCap.center != defaultCap.center {
        t.Error("empty Caps should be have the same center as the default")
    }
    if emptyCap.Height() != defaultCap.Height() {
        t.Error("empty Caps should be have the same height as the default")
    }

    if yAxis.Height() != zeroHeight {
        t.Error("y-axis cap should not be empty height")
    }

    if xAxis.Height() != zeroHeight {
        t.Error("x-axis cap should not be empty height")
    }
    if xAxis.Radius().Radians() != zeroHeight {
        t.Errorf("radius of x-axis cap got %f want %f", xAxis.Radius().Radians(), emptyHeight)
    }

    hc := Point{hemi.center.Mul(-1.0)}
    if hc != hemi.Complement().center {
        t.Error("hemi center and its complement should have the same center")
    }
    if hemi.Height() != 1.0 {
        t.Error("hemi cap should be 1.0 in height")
    }
}

func TestCapContains(t *testing.T) {
    tests := []struct {
        c1, c2 Cap
        want   bool
    }{
        {emptyCap, emptyCap, true},
        {fullCap, emptyCap, true},
        {fullCap, fullCap, true},
        {emptyCap, xAxis, false},
        {fullCap, xAxis, true},
        {xAxis, fullCap, false},
        {xAxis, xAxis, true},
        {xAxis, emptyCap, true},
        {hemi, tiny, true},
        {hemi, CapFromCenterAngle(xAxisPt, s1.Angle(math.Pi/4-epsilon)), true},
        {hemi, CapFromCenterAngle(xAxisPt, s1.Angle(math.Pi/4+epsilon)), false},
        {concave, hemi, true},
        {concave, CapFromCenterHeight(Point{concave.center.Mul(-1.0)}, 0.1), false},
    }
    for _, test := range tests {
        if got := test.c1.Contains(test.c2); got != test.want {
            t.Errorf("%v.Contains(%v) = %t; want %t", test.c1, test.c2, got, test.want)
        }
    }
}

func TestCapContainsPoint(t *testing.T) {
    // We don't use the standard epsilon in this test due different compiler
    // math optimizations that are permissible (FMA vs no FMA) that yield
    // slightly different floating point results between gccgo and gc.
    const epsilon = 1e-14
    tangent := tiny.center.Cross(r3.Vector{3, 2, 1}).Normalize()
    tests := []struct {
        c    Cap
        p    Point
        want bool
    }{
        {xAxis, xAxisPt, true},
        {xAxis, Point{r3.Vector{1, 1e-20, 0}}, false},
        {yAxis, xAxis.center, false},
        {xComp, xAxis.center, true},
        {xComp.Complement(), xAxis.center, false},
        {tiny, Point{tiny.center.Add(tangent.Mul(tinyRad * 0.99))}, true},
        {tiny, Point{tiny.center.Add(tangent.Mul(tinyRad * 1.01))}, false},
        {hemi, PointFromCoords(1, 0, -(1 - epsilon)), true},
        {hemi, xAxisPt, true},
        {hemi.Complement(), xAxisPt, false},
        {concave, PointFromLatLng(LatLngFromDegrees(-70*(1-epsilon), 10)), true},
        {concave, PointFromLatLng(LatLngFromDegrees(-70*(1+epsilon), 10)), false},
        // This test case is the one where the floating point values end up
        // different in the 15th place and beyond.
        {concave, PointFromLatLng(LatLngFromDegrees(-50*(1-epsilon), -170)), true},
        {concave, PointFromLatLng(LatLngFromDegrees(-50*(1+epsilon), -170)), false},
    }
    for _, test := range tests {
        if got := test.c.ContainsPoint(test.p); got != test.want {
            t.Errorf("%v.ContainsPoint(%v) = %t, want %t", test.c, test.p, got, test.want)
        }
    }
}

func TestCapInteriorIntersects(t *testing.T) {
    tests := []struct {
        c1, c2 Cap
        want   bool
    }{
        {emptyCap, emptyCap, false},
        {emptyCap, xAxis, false},
        {fullCap, emptyCap, false},
        {fullCap, fullCap, true},
        {fullCap, xAxis, true},
        {xAxis, fullCap, false},
        {xAxis, xAxis, false},
        {xAxis, emptyCap, false},
        {concave, hemi.Complement(), true},
    }
    for _, test := range tests {
        if got := test.c1.InteriorIntersects(test.c2); got != test.want {
            t.Errorf("%v.InteriorIntersects(%v); got %t want %t", test.c1, test.c2, got, test.want)
        }
    }
}

func TestCapInteriorContains(t *testing.T) {
    if hemi.InteriorContainsPoint(Point{r3.Vector{1, 0, -(1 + epsilon)}}) {
        t.Errorf("hemi (%v) should not contain point just past half way(%v)", hemi,
            Point{r3.Vector{1, 0, -(1 + epsilon)}})
    }
}

func TestCapExpanded(t *testing.T) {
    cap50 := CapFromCenterAngle(xAxisPt, 50.0*s1.Degree)
    cap51 := CapFromCenterAngle(xAxisPt, 51.0*s1.Degree)

    if !emptyCap.Expanded(s1.Angle(fullHeight)).IsEmpty() {
        t.Error("Expanding empty cap should return an empty cap")
    }
    if !fullCap.Expanded(s1.Angle(fullHeight)).IsFull() {
        t.Error("Expanding a full cap should return an full cap")
    }

    if !cap50.Expanded(0).ApproxEqual(cap50) {
        t.Error("Expanding a cap by 0° should be equal to the original")
    }
    if !cap50.Expanded(1 * s1.Degree).ApproxEqual(cap51) {
        t.Error("Expanding 50° by 1° should equal the 51° cap")
    }

    if cap50.Expanded(129.99 * s1.Degree).IsFull() {
        t.Error("Expanding 50° by 129.99° should not give a full cap")
    }
    if !cap50.Expanded(130.01 * s1.Degree).IsFull() {
        t.Error("Expanding 50° by 130.01° should give a full cap")
    }
}

func TestCapRadiusToHeight(t *testing.T) {
    tests := []struct {
        got  s1.Angle
        want float64
    }{
        // Above/below boundary checks.
        {s1.Angle(-0.5), emptyHeight},
        {s1.Angle(0), 0},
        {s1.Angle(math.Pi), fullHeight},
        {s1.Angle(2 * math.Pi), fullHeight},
        // Degree tests.
        {-7.0 * s1.Degree, emptyHeight},
        {-0.0 * s1.Degree, 0},
        {0.0 * s1.Degree, 0},
        {12.0 * s1.Degree, 0.0218523992661943},
        {30.0 * s1.Degree, 0.1339745962155613},
        {45.0 * s1.Degree, 0.2928932188134525},
        {90.0 * s1.Degree, 1.0},
        {179.99 * s1.Degree, 1.9999999847691292},
        {180.0 * s1.Degree, fullHeight},
        {270.0 * s1.Degree, fullHeight},
        // Radians tests.
        {-1.0 * s1.Radian, emptyHeight},
        {-0.0 * s1.Radian, 0},
        {0.0 * s1.Radian, 0},
        {1.0 * s1.Radian, 0.45969769413186},
        {math.Pi / 2.0 * s1.Radian, 1.0},
        {2.0 * s1.Radian, 1.4161468365471424},
        {3.0 * s1.Radian, 1.9899924966004454},
        {math.Pi * s1.Radian, fullHeight},
        {4.0 * s1.Radian, fullHeight},
    }
    for _, test := range tests {
        // float64Eq comes from s2latlng_test.go
        if got := radiusToHeight(test.got); !float64Eq(got, test.want) {
            t.Errorf("radiusToHeight(%v) = %v; want %v", test.got, got, test.want)
        }
    }
}

func TestCapRectBounds(t *testing.T) {
    const epsilon = 1e-13
    var tests = []struct {
        desc     string
        have     Cap
        latLoDeg float64
        latHiDeg float64
        lngLoDeg float64
        lngHiDeg float64
        isFull   bool
    }{
        {
            "Cap that includes South Pole.",
            CapFromCenterAngle(PointFromLatLng(LatLngFromDegrees(-45, 57)), s1.Degree*50),
            -90, 5, -180, 180, true,
        },
        {
            "Cap that is tangent to the North Pole.",
            CapFromCenterAngle(PointFromCoords(1, 0, 1), s1.Radian*(math.Pi/4.0+1e-16)),
            0, 90, -180, 180, true,
        },
        {
            "Cap that at 45 degree center that goes from equator to the pole.",
            CapFromCenterAngle(PointFromCoords(1, 0, 1), s1.Degree*(45+5e-15)),
            0, 90, -180, 180, true,
        },
        {
            "The eastern hemisphere.",
            CapFromCenterAngle(Point{r3.Vector{0, 1, 0}}, s1.Radian*(math.Pi/2+2e-16)),
            -90, 90, -180, 180, true,
        },
        {
            "A cap centered on the equator.",
            CapFromCenterAngle(PointFromLatLng(LatLngFromDegrees(0, 50)), s1.Degree*20),
            -20, 20, 30, 70, false,
        },
        {
            "A cap centered on the North Pole.",
            CapFromCenterAngle(PointFromLatLng(LatLngFromDegrees(90, 123)), s1.Degree*10),
            80, 90, -180, 180, true,
        },
    }

    for _, test := range tests {
        r := test.have.RectBound()
        if !float64Near(s1.Angle(r.Lat.Lo).Degrees(), test.latLoDeg, epsilon) {
            t.Errorf("%s: %v.RectBound(), Lat.Lo not close enough, got %0.20f, want %0.20f",
                test.desc, test.have, s1.Angle(r.Lat.Lo).Degrees(), test.latLoDeg)
        }
        if !float64Near(s1.Angle(r.Lat.Hi).Degrees(), test.latHiDeg, epsilon) {
            t.Errorf("%s: %v.RectBound(), Lat.Hi not close enough, got %0.20f, want %0.20f",
                test.desc, test.have, s1.Angle(r.Lat.Hi).Degrees(), test.latHiDeg)
        }
        if !float64Near(s1.Angle(r.Lng.Lo).Degrees(), test.lngLoDeg, epsilon) {
            t.Errorf("%s: %v.RectBound(), Lng.Lo not close enough, got %0.20f, want %0.20f",
                test.desc, test.have, s1.Angle(r.Lng.Lo).Degrees(), test.lngLoDeg)
        }
        if !float64Near(s1.Angle(r.Lng.Hi).Degrees(), test.lngHiDeg, epsilon) {
            t.Errorf("%s: %v.RectBound(), Lng.Hi not close enough, got %0.20f, want %0.20f",
                test.desc, test.have, s1.Angle(r.Lng.Hi).Degrees(), test.lngHiDeg)
        }
        if got := r.Lng.IsFull(); got != test.isFull {
            t.Errorf("%s: RectBound(%v).isFull() = %t, want %t", test.desc, test.have, got, test.isFull)
        }
    }

    // Empty and full caps.
    if !EmptyCap().RectBound().IsEmpty() {
        t.Errorf("RectBound() on EmptyCap should be empty.")
    }

    if !FullCap().RectBound().IsFull() {
        t.Errorf("RectBound() on FullCap should be full.")
    }
}

func TestCapAddPoint(t *testing.T) {
    const epsilon = 1e-14
    tests := []struct {
        have Cap
        p    Point
        want Cap
    }{
        // Cap plus its center equals itself.
        {xAxis, xAxisPt, xAxis},
        {yAxis, yAxisPt, yAxis},

        // Cap plus opposite point equals full.
        {xAxis, Point{r3.Vector{-1, 0, 0}}, fullCap},
        {yAxis, Point{r3.Vector{0, -1, 0}}, fullCap},

        // Cap plus orthogonal axis equals half cap.
        {xAxis, Point{r3.Vector{0, 0, 1}}, CapFromCenterAngle(xAxisPt, s1.Angle(math.Pi/2.0))},
        {xAxis, Point{r3.Vector{0, 0, -1}}, CapFromCenterAngle(xAxisPt, s1.Angle(math.Pi/2.0))},

        // The 45 degree angled hemisphere plus some points.
        {
            hemi,
            PointFromCoords(0, 1, -1),
            CapFromCenterAngle(Point{r3.Vector{1, 0, 1}},
                s1.Angle(120.0)*s1.Degree),
        },
        {
            hemi,
            PointFromCoords(0, -1, -1),
            CapFromCenterAngle(Point{r3.Vector{1, 0, 1}},
                s1.Angle(120.0)*s1.Degree),
        },
        {
            hemi,
            PointFromCoords(-1, -1, -1),
            CapFromCenterAngle(Point{r3.Vector{1, 0, 1}},
                s1.Angle(math.Acos(-math.Sqrt(2.0/3.0)))),
        },
        {hemi, Point{r3.Vector{0, 1, 1}}, hemi},
        {hemi, Point{r3.Vector{1, 0, 0}}, hemi},
    }

    for _, test := range tests {
        got := test.have.AddPoint(test.p)
        if !got.ApproxEqual(test.want) {
            t.Errorf("%v.AddPoint(%v) = %v, want %v", test.have, test.p, got, test.want)
        }

        if !got.ContainsPoint(test.p) {
            t.Errorf("%v.AddPoint(%v) did not contain added point", test.have, test.p)
        }
    }
}

func TestCapAddCap(t *testing.T) {
    tests := []struct {
        have  Cap
        other Cap
        want  Cap
    }{
        // Identity cases.
        {emptyCap, emptyCap, emptyCap},
        {fullCap, fullCap, fullCap},

        // Anything plus empty equals itself.
        {fullCap, emptyCap, fullCap},
        {emptyCap, fullCap, fullCap},
        {xAxis, emptyCap, xAxis},
        {emptyCap, xAxis, xAxis},
        {yAxis, emptyCap, yAxis},
        {emptyCap, yAxis, yAxis},

        // Two halves make a whole.
        {xAxis, xComp, fullCap},

        // Two zero-height orthogonal axis caps make a half-cap.
        {xAxis, yAxis, CapFromCenterAngle(xAxisPt, s1.Angle(math.Pi/2.0))},
    }

    for _, test := range tests {
        got := test.have.AddCap(test.other)
        if !got.ApproxEqual(test.want) {
            t.Errorf("%v.AddCap(%v) = %v, want %v", test.have, test.other, got, test.want)
        }
    }
}

func TestCapContainsCell(t *testing.T) {
    faceRadius := math.Atan(math.Sqrt2)
    for face := 0; face < 6; face++ {
        // The cell consisting of the entire face.
        rootCell := CellFromCellID(CellIDFromFace(face))

        // A leaf cell at the midpoint of the v=1 edge.
        edgeCell := CellFromPoint(Point{faceUVToXYZ(face, 0, 1-epsilon)})

        // A leaf cell at the u=1, v=1 corner
        cornerCell := CellFromPoint(Point{faceUVToXYZ(face, 1-epsilon, 1-epsilon)})

        // Quick check for full and empty caps.
        if !fullCap.ContainsCell(rootCell) {
            t.Errorf("Cap(%v).ContainsCell(%v) = %t; want = %t", fullCap, rootCell, false, true)
        }

        // Check intersections with the bounding caps of the leaf cells that are adjacent to
        // cornerCell along the Hilbert curve.  Because this corner is at (u=1,v=1), the curve
        // stays locally within the same cube face.
        first := cornerCell.id.Advance(-3)
        last := cornerCell.id.Advance(4)
        for id := first; id < last; id = id.Next() {
            c := CellFromCellID(id).CapBound()
            if got, want := c.ContainsCell(cornerCell), id == cornerCell.id; got != want {
                t.Errorf("Cap(%v).ContainsCell(%v) = %t; want = %t", c, cornerCell, got, want)
            }
        }

        for capFace := 0; capFace < 6; capFace++ {
            // A cap that barely contains all of capFace.
            center := unitNorm(capFace)
            covering := CapFromCenterAngle(center, s1.Angle(faceRadius+epsilon))
            if got, want := covering.ContainsCell(rootCell), capFace == face; got != want {
                t.Errorf("Cap(%v).ContainsCell(%v) = %t; want = %t", covering, rootCell, got, want)
            }
            if got, want := covering.ContainsCell(edgeCell), center.Vector.Dot(edgeCell.id.Point().Vector) > 0.1; got != want {
                t.Errorf("Cap(%v).ContainsCell(%v) = %t; want = %t", covering, edgeCell, got, want)
            }
            if got, want := covering.ContainsCell(edgeCell), covering.IntersectsCell(edgeCell); got != want {
                t.Errorf("Cap(%v).ContainsCell(%v) = %t; want = %t", covering, edgeCell, got, want)
            }
            if got, want := covering.ContainsCell(cornerCell), capFace == face; got != want {
                t.Errorf("Cap(%v).ContainsCell(%v) = %t; want = %t", covering, cornerCell, got, want)
            }

            // A cap that barely intersects the edges of capFace.
            bulging := CapFromCenterAngle(center, s1.Angle(math.Pi/4+epsilon))
            if bulging.ContainsCell(rootCell) {
                t.Errorf("Cap(%v).ContainsCell(%v) = %t; want = %t", bulging, rootCell, true, false)
            }
            if got, want := bulging.ContainsCell(edgeCell), capFace == face; got != want {
                t.Errorf("Cap(%v).ContainsCell(%v) = %t; want = %t", bulging, edgeCell, got, want)
            }
            if bulging.ContainsCell(cornerCell) {
                t.Errorf("Cap(%v).ContainsCell(%v) = %t; want = %t", bulging, cornerCell, true, false)
            }
        }
    }
}

func TestCapIntersectsCell(t *testing.T) {
    faceRadius := math.Atan(math.Sqrt2)
    for face := 0; face < 6; face++ {
        // The cell consisting of the entire face.
        rootCell := CellFromCellID(CellIDFromFace(face))

        // A leaf cell at the midpoint of the v=1 edge.
        edgeCell := CellFromPoint(Point{faceUVToXYZ(face, 0, 1-epsilon)})

        // A leaf cell at the u=1, v=1 corner
        cornerCell := CellFromPoint(Point{faceUVToXYZ(face, 1-epsilon, 1-epsilon)})

        // Quick check for full and empty caps.
        if emptyCap.IntersectsCell(rootCell) {
            t.Errorf("Cap(%v).IntersectsCell(%v) = %t; want = %t", emptyCap, rootCell, true, false)
        }

        // Check intersections with the bounding caps of the leaf cells that are adjacent to
        // cornerCell along the Hilbert curve.  Because this corner is at (u=1,v=1), the curve
        // stays locally within the same cube face.
        first := cornerCell.id.Advance(-3)
        last := cornerCell.id.Advance(4)
        for id := first; id < last; id = id.Next() {
            c := CellFromCellID(id).CapBound()
            if got, want := c.IntersectsCell(cornerCell), id.immediateParent().Contains(cornerCell.id); got != want {
                t.Errorf("Cap(%v).IntersectsCell(%v) = %t; want = %t", c, cornerCell, got, want)
            }
        }

        antiFace := (face + 3) % 6
        for capFace := 0; capFace < 6; capFace++ {
            // A cap that barely contains all of capFace.
            center := unitNorm(capFace)
            covering := CapFromCenterAngle(center, s1.Angle(faceRadius+epsilon))
            if got, want := covering.IntersectsCell(rootCell), capFace != antiFace; got != want {
                t.Errorf("Cap(%v).IntersectsCell(%v) = %t; want = %t", covering, rootCell, got, want)
            }
            if got, want := covering.IntersectsCell(edgeCell), covering.ContainsCell(edgeCell); got != want {
                t.Errorf("Cap(%v).IntersectsCell(%v) = %t; want = %t", covering, edgeCell, got, want)
            }
            if got, want := covering.IntersectsCell(cornerCell),
            center.Vector.Dot(cornerCell.id.Point().Vector) > 0; got != want {
                t.Errorf("Cap(%v).IntersectsCell(%v) = %t; want = %t", covering, cornerCell, got, want)
            }

            // A cap that barely intersects the edges of capFace.
            bulging := CapFromCenterAngle(center, s1.Angle(math.Pi/4+epsilon))
            if got, want := bulging.IntersectsCell(rootCell), capFace != antiFace; got != want {
                t.Errorf("Cap(%v).IntersectsCell(%v) = %t; want = %t", bulging, rootCell, got, want)
            }
            if got, want := bulging.IntersectsCell(edgeCell), center.Vector.Dot(edgeCell.id.Point().Vector) > 0.1; got != want {
                t.Errorf("Cap(%v).IntersectsCell(%v) = %t; want = %t", bulging, edgeCell, got, want)
            }
            if bulging.IntersectsCell(cornerCell) {
                t.Errorf("Cap(%v).IntersectsCell(%v) = %t; want = %t", bulging, cornerCell, true, false)
            }

            // A singleton cap.
            singleton := CapFromCenterAngle(center, 0)
            if got, want := singleton.IntersectsCell(rootCell), capFace == face; got != want {
                t.Errorf("Cap(%v).IntersectsCell(%v) = %t; want = %t", singleton, rootCell, got, want)
            }
            if singleton.IntersectsCell(edgeCell) {
                t.Errorf("Cap(%v).IntersectsCell(%v) = %t; want = %t", singleton, edgeCell, true, false)
            }
            if singleton.IntersectsCell(cornerCell) {
                t.Errorf("Cap(%v).IntersectsCell(%v) = %t; want = %t", singleton, cornerCell, true, false)
            }
        }
    }
}

func TestCapCentroid(t *testing.T) {
    // Empty and full caps.
    if got, want := EmptyCap().Centroid(), (Point{}); !got.ApproxEqual(want) {
        t.Errorf("Centroid of EmptyCap should be zero point, got %v", want)
    }
    if got, want := FullCap().Centroid().Norm(), 1e-15; got > want {
        t.Errorf("Centroid of FullCap should have a Norm of 0, got %v", want)
    }

    // Random caps.
    for i := 0; i < 100; i++ {
        center := randomPoint()
        height := randomUniformFloat64(0.0, 2.0)
        c := CapFromCenterHeight(center, height)
        got := c.Centroid()
        want := center.Mul((1.0 - height/2.0) * c.Area())
        if delta := got.Sub(want).Norm(); delta > 1e-15 {
            t.Errorf("%v.Sub(%v).Norm() = %v, want %v", got, want, delta, 1e-15)
        }
    }
}

func TestCapUnion(t *testing.T) {
    // Two caps which have the same center but one has a larger radius.
    a := CapFromCenterAngle(PointFromLatLng(LatLngFromDegrees(50.0, 10.0)), s1.Degree*0.2)
    b := CapFromCenterAngle(PointFromLatLng(LatLngFromDegrees(50.0, 10.0)), s1.Degree*0.3)
    if !b.Contains(a) {
        t.Errorf("%v.Contains(%v) = false, want true", b, a)
    }
    if got := b.ApproxEqual(a.Union(b)); !got {
        t.Errorf("%v.ApproxEqual(%v) = %v, want true", b, a.Union(b), got)
    }

    // Two caps where one is the full cap.
    if got := a.Union(FullCap()); !got.IsFull() {
        t.Errorf("%v.Union(%v).IsFull() = %v, want true", a, got, got.IsFull())
    }

    // Two caps where one is the empty cap.
    if got := a.Union(EmptyCap()); !a.ApproxEqual(got) {
        t.Errorf("%v.Union(EmptyCap) = %v, want %v", a, got, a)
    }

    // Two caps which have different centers, one entirely encompasses the other.
    c := CapFromCenterAngle(PointFromLatLng(LatLngFromDegrees(51.0, 11.0)), s1.Degree*1.5)
    if !c.Contains(a) {
        t.Errorf("%v.Contains(%v) = false, want true", c, a)
    }
    if got := a.Union(c).center; !got.ApproxEqual(c.center) {
        t.Errorf("%v.Union(%v).center = %v, want %v", a, c, got, c.center)
    }
    if got := a.Union(c); !float64Eq(float64(got.Radius()), float64(c.Radius())) {
        t.Errorf("%v.Union(%v).Radius = %v, want %v", a, c, got.Radius(), c.Radius())
    }

    // Two entirely disjoint caps.
    d := CapFromCenterAngle(PointFromLatLng(LatLngFromDegrees(51.0, 11.0)), s1.Degree*0.1)
    if d.Contains(a) {
        t.Errorf("%v.Contains(%v) = true, want false", d, a)
    }
    if d.Intersects(a) {
        t.Errorf("%v.Intersects(%v) = true, want false", d, a)
    }

    // Check union and reverse direction are the same.
    aUnionD := a.Union(d)
    if !aUnionD.ApproxEqual(d.Union(a)) {
        t.Errorf("%v.Union(%v).ApproxEqual(%v.Union(%v)) = false, want true", a, d, d, a)
    }
    if got, want := LatLngFromPoint(aUnionD.center).Lat.Degrees(), 50.4588; !float64Near(got, want, 0.001) {
        t.Errorf("%v.Center.Lat = %v, want %v", aUnionD, got, want)
    }
    if got, want := LatLngFromPoint(aUnionD.center).Lng.Degrees(), 10.4525; !float64Near(got, want, 0.001) {
        t.Errorf("%v.Center.Lng = %v, want %v", aUnionD, got, want)
    }
    if got, want := aUnionD.Radius().Degrees(), 0.7425; !float64Near(got, want, 0.001) {
        t.Errorf("%v.Radius = %v, want %v", aUnionD, got, want)
    }

    // Two partially overlapping caps.
    e := CapFromCenterAngle(PointFromLatLng(LatLngFromDegrees(50.3, 10.3)), s1.Degree*0.2)
    aUnionE := a.Union(e)
    if e.Contains(a) {
        t.Errorf("%v.Contains(%v) = false, want true", e, a)
    }
    if !e.Intersects(a) {
        t.Errorf("%v.Intersects(%v) = false, want true", e, a)
    }
    if !aUnionE.ApproxEqual(e.Union(a)) {
        t.Errorf("%v.Union(%v).ApproxEqual(%v.Union(%v)) = false, want true", a, e, e, a)
    }
    if got, want := LatLngFromPoint(aUnionE.center).Lat.Degrees(), 50.1500; !float64Near(got, want, 0.001) {
        t.Errorf("%v.Center.Lat = %v, want %v", aUnionE, got, want)
    }
    if got, want := LatLngFromPoint(aUnionE.center).Lng.Degrees(), 10.1495; !float64Near(got, want, 0.001) {
        t.Errorf("%v.Center.Lng = %v, want %v", aUnionE, got, want)
    }
    if got, want := aUnionE.Radius().Degrees(), 0.3781; !float64Near(got, want, 0.001) {
        t.Errorf("%v.Radius = %v, want %v", aUnionE, got, want)
    }

    p1 := Point{r3.Vector{0, 0, 1}}
    p2 := Point{r3.Vector{0, 1, 0}}
    // Two very large caps, whose radius sums to in excess of 180 degrees, and
    // whose centers are not antipodal.
    f := CapFromCenterAngle(p1, s1.Degree*150)
    g := CapFromCenterAngle(p2, s1.Degree*150)
    if !f.Union(g).IsFull() {
        t.Errorf("%v.Union(%v).IsFull() = false, want true", f, g)
    }

    // Two non-overlapping hemisphere caps with antipodal centers.
    hemi := CapFromCenterHeight(p1, 1)
    if !hemi.Union(hemi.Complement()).IsFull() {
        t.Errorf("%v.Union(%v).Complement().IsFull() = false, want true", hemi, hemi.Complement())
    }
}

func TestCapEqual(t *testing.T) {
    tests := []struct {
        a, b Cap
        want bool
    }{
        {EmptyCap(), EmptyCap(), true},
        {EmptyCap(), FullCap(), false},
        {FullCap(), FullCap(), true},
        {
            CapFromCenterAngle(PointFromCoords(0, 0, 1), s1.Degree*150),
            CapFromCenterAngle(PointFromCoords(0, 0, 1), s1.Degree*151),
            false,
        },
        {xAxis, xAxis, true},
        {xAxis, yAxis, false},
        {xComp, xAxis.Complement(), true},
    }

    for _, test := range tests {
        if got := test.a.Equal(test.b); got != test.want {
            t.Errorf("%v.Equal(%v) = %t, want %t", test.a, test.b, got, test.want)
        }
    }
}
*/
