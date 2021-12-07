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

use crate::consts::*;
use crate::r1;
use crate::r2;
use crate::s1;
use crate::s1::*;
use crate::s2;
use crate::s2::cap::Cap;
use crate::s2::cellid::*;
use crate::s2::latlng::*;
use crate::s2::metric::*;
use crate::s2::point::*;
use crate::s2::region::Region;
use crate::s2::stuv::*;
use std::f64::consts::PI;

lazy_static! {
    static ref POLE_MIN_LAT: f64 = (1. / 3f64).sqrt().asin() - 0.5 * DBL_EPSILON;
}

/// Cell is an S2 region object that represents a cell. Unlike CellIDs,
/// it supports efficient containment and intersection tests. However, it is
/// also a more expensive representation.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Cell {
    face: u8,
    level: u8,
    pub orientation: u8,
    pub id: CellID,
    pub uv: r2::rect::Rect,
}

impl<'a> From<&'a CellID> for Cell {
    fn from(id: &'a CellID) -> Self {
        let (f, i, j, o) = id.face_ij_orientation();
        assert!(f < 6);
        let level = id.level();
        Cell {
            face: f as u8,
            level: level as u8,
            orientation: o as u8,
            id: *id,
            uv: ij_level_to_bound_uv(i, j, level),
        }
    }
}
impl From<CellID> for Cell {
    fn from(id: CellID) -> Self {
        Self::from(&id)
    }
}

impl<'a> From<&'a Point> for Cell {
    fn from(p: &'a Point) -> Self {
        Cell::from(CellID::from(p))
    }
}
impl From<Point> for Cell {
    fn from(p: Point) -> Self {
        Self::from(&p)
    }
}

impl<'a> From<&'a LatLng> for Cell {
    fn from(ll: &'a LatLng) -> Self {
        Self::from(CellID::from(ll))
    }
}
impl From<LatLng> for Cell {
    fn from(ll: LatLng) -> Self {
        Self::from(&ll)
    }
}

impl<'a> From<&'a Cell> for CellID {
    fn from(c: &'a Cell) -> Self {
        c.id
    }
}
impl From<Cell> for CellID {
    fn from(c: Cell) -> Self {
        Self::from(&c)
    }
}

impl Cell {
    pub fn face(&self) -> u8 {
        self.face
    }

    pub fn level(&self) -> u8 {
        self.level
    }

    pub fn is_leaf(&self) -> bool {
        self.level == MAX_LEVEL as u8
    }

    pub fn size_ij(&self) -> u64 {
        size_ij(u64::from(self.level))
    }

    /// vertex returns the k-th vertex of the cell (k = 0,1,2,3) in CCW order
    /// (lower left, lower right, upper right, upper left in the UV plane).
    pub fn vertex(&self, k: usize) -> Point {
        let v = &self.uv.vertices()[k];
        Point(face_uv_to_xyz(self.face, v.x, v.y).normalize())
    }

    pub fn vertices(&self) -> [Point; 4] {
        let verts = self.uv.vertices();
        [
            Point(face_uv_to_xyz(self.face, verts[0].x, verts[0].y).normalize()),
            Point(face_uv_to_xyz(self.face, verts[1].x, verts[1].y).normalize()),
            Point(face_uv_to_xyz(self.face, verts[2].x, verts[2].y).normalize()),
            Point(face_uv_to_xyz(self.face, verts[3].x, verts[3].y).normalize()),
        ]
    }

    /// edge returns the inward-facing normal of the great circle passing through
    /// the CCW ordered edge from vertex k to vertex k+1 (mod 4) (for k = 0,1,2,3).
    pub fn edge(&self, k: usize) -> Point {
        match k {
            0 => Point(vnorm(self.face, self.uv.y.lo).normalize()),
            1 => Point(unorm(self.face, self.uv.x.hi).normalize()),
            2 => Point((vnorm(self.face, self.uv.y.hi) * -1.).normalize()),
            3 => Point((unorm(self.face, self.uv.x.lo) * -1.).normalize()),
            _ => unimplemented!(),
        }
    }

    /// bound_uv returns the bounds of this cell in (u,v)-space.
    pub fn bound_uv(&self) -> &r2::rect::Rect {
        &self.uv
    }

    /// center returns the direction vector corresponding to the center in
    /// (s,t)-space of the given cell. This is the point at which the cell is
    /// divided into four subcells; it is not necessarily the centroid of the
    /// cell in (u,v)-space or (x,y,z)-space
    pub fn center(&self) -> Point {
        Point(self.id.raw_point().normalize())
    }

    /// Children returns the four direct children of this cell in traversal order
    /// and returns true. If this is a leaf cell, or the children could not be created,
    /// false is returned.
    /// The C++ method is called Subdivide.
    pub fn children(&self) -> Option<[Cell; 4]> {
        //TODO: fix redundent copy
        if self.is_leaf() {
            return None;
        }
        //TODO
        let mut children = [self.clone(), self.clone(), self.clone(), self.clone()];

        let uv_mid = self.id.center_uv();

        let mut cid = self.id.child_begin();
        for pos in 0..4 {
            children[pos] = Cell {
                face: self.face,
                level: self.level + 1,
                orientation: self.orientation ^ (POS_TO_ORIENTATION[pos]),
                id: cid,
                uv: self.uv.clone(),
            };

            // We want to split the cell in half in u and v. To decide which
            // side to set equal to the midpoint value, we look at cell's (i,j)
            // position within its parent. The index for i is in bit 1 of ij.
            let ij = POS_TO_IJ[self.orientation as usize][pos];
            let i = ij >> 1;
            let j = ij & 1;
            if i == 1 {
                children[pos].uv.x.hi = self.uv.x.hi;
                children[pos].uv.x.lo = uv_mid.x;
            } else {
                children[pos].uv.x.lo = self.uv.x.lo;
                children[pos].uv.x.hi = uv_mid.x;
            }
            if j == 1 {
                children[pos].uv.y.hi = self.uv.y.hi;
                children[pos].uv.y.lo = uv_mid.y;
            } else {
                children[pos].uv.y.lo = self.uv.y.lo;
                children[pos].uv.y.hi = uv_mid.y;
            }
            cid = cid.next();
        }

        Some(children)
    }

    /// exact_area returns the area of this cell as accurately as possible.
    pub fn exact_area(&self) -> f64 {
        let verts = self.vertices();
        point_area(&verts[0], &verts[1], &verts[2]) + point_area(&verts[0], &verts[2], &verts[3])
    }

    /// approx_area returns the approximate area of this cell. This method is accurate
    /// to within 3% percent for all cell sizes and accurate to within 0.1% for cells
    /// at level 5 or higher (i.e. squares 350km to a side or smaller on the Earth's
    /// surface). It is moderately cheap to compute.
    pub fn approx_area(&self) -> f64 {
        // All cells at the first two levels have the same area.
        if self.level < 2 {
            return self.average_area();
        }

        // First, compute the approximate area of the cell when projected
        // perpendicular to its normal. The cross product of its diagonals gives
        // the normal, and the length of the normal is twice the projected area.
        let verts = self.vertices();
        let flat_area = 0.5
            * (&verts[2] - &verts[0])
                .0
                .cross(&(&verts[3] - &verts[1]).0)
                .norm();

        // Now, compensate for the curvature of the cell surface by pretending
        // that the cell is shaped like a spherical cap. The ratio of the
        // area of a spherical cap to the area of its projected disc turns out
        // to be 2 / (1 + sqrt(1 - r*r)) where r is the radius of the disself.
        // For example, when r=0 the ratio is 1, and when r=1 the ratio is 2.
        // Here we set Pi*r*r == flat_area to find the equivalent disself.
        flat_area * 2. / (1. + (1. - (1. / PI * flat_area).min(1.)).sqrt())
    }

    /// average_area returns the average area of cells at the level of this cell.
    /// This is accurate to within a factor of 1.7.
    pub fn average_area(&self) -> f64 {
        AVG_AREAMETRIC.value(self.level)
    }

    fn uv_from_ij(&self, i: i32, j: i32) -> (f64, f64) {
        match (i, j) {
            (0, 0) => (self.uv.x.lo, self.uv.y.lo),
            (0, 1) => (self.uv.x.lo, self.uv.y.hi),
            (1, 0) => (self.uv.x.hi, self.uv.y.lo),
            (1, 1) => (self.uv.x.hi, self.uv.y.hi),
            _ => panic!("i and/or j is out of bound"),
        }
    }

    fn point_from_ij(&self, i: i32, j: i32) -> Point {
        let (u, v) = self.uv_from_ij(i, j);
        Point(face_uv_to_xyz(self.face, u, v))
    }

    /// latitude returns the latitude of the cell vertex given by (i,j), where "i" and "j" are either 0 or 1.
    pub fn latitude(&self, i: i32, j: i32) -> Angle {
        self.point_from_ij(i, j).latitude()
    }

    /// longitude returns the longitude of the cell vertex given by (i,j), where "i" and "j" are either 0 or 1.
    pub fn longitude(&self, i: i32, j: i32) -> Angle {
        self.point_from_ij(i, j).longitude()
    }

    /// rect_bound returns the bounding rectangle of this cell.
    pub fn rect_bound(&self) -> s2::rect::Rect {
        if self.level > 0 {
            // Except for cells at level 0, the latitude and longitude extremes are
            // attained at the vertices.  Furthermore, the latitude range is
            // determined by one pair of diagonally opposite vertices and the
            // longitude range is determined by the other pair.
            //
            // We first determine which corner (i,j) of the cell has the largest
            // absolute latitude.  To maximize latitude, we want to find the point in
            // the cell that has the largest absolute z-coordinate and the smallest
            // absolute x- and y-coordinates.  To do this we look at each coordinate
            // (u and v), and determine whether we want to minimize or maximize that
            // coordinate based on the axis direction and the cell's (u,v) quadrant.
            let u = self.uv.x.lo + self.uv.x.hi;
            let v = self.uv.y.lo + self.uv.y.hi;
            let i = if u_axis(self.face).0.z == 0. {
                if u < 0. {
                    1
                } else {
                    0
                }
            } else {
                if u > 0. {
                    1
                } else {
                    0
                }
            };
            let j = if v_axis(self.face).0.z == 0. {
                if v < 0. {
                    1
                } else {
                    0
                }
            } else {
                if v > 0. {
                    1
                } else {
                    0
                }
            };

            let lat = r1::interval::Interval::from_point(self.latitude(i, j).rad())
                + self.latitude(1 - i, 1 - j).rad();
            let lng = s1::interval::EMPTY
                + self.longitude(i, 1 - j).rad()
                + self.longitude(1 - i, j).rad();

            // We grow the bounds slightly to make sure that the bounding rectangle
            // contains LatLngFromPoint(P) for any point P inside the loop L defined by the
            // four *normalized* vertices.  Note that normalization of a vector can
            // change its direction by up to 0.5 * DBL_EPSILON radians, and it is not
            // enough just to add Normalize calls to the code above because the
            // latitude/longitude ranges are not necessarily determined by diagonally
            // opposite vertex pairs after normalization.
            //
            // We would like to bound the amount by which the latitude/longitude of a
            // contained point P can exceed the bounds computed above.  In the case of
            // longitude, the normalization error can change the direction of rounding
            // leading to a maximum difference in longitude of 2 * DBL_EPSILON.  In
            // the case of latitude, the normalization error can shift the latitude by
            // up to 0.5 * DBL_EPSILON and the other sources of error can cause the
            // two latitudes to differ by up to another 1.5 * DBL_EPSILON, which also
            // leads to a maximum difference of 2 * DBL_EPSILON.
            let max_err = Angle::from(Rad(2. * DBL_EPSILON));
            return s2::rect::Rect { lat, lng }
                .expanded(&LatLng {
                    lat: max_err,
                    lng: max_err,
                })
                .polar_closure();
        }

        // The 4 cells around the equator extend to +/-45 degrees latitude at the
        // midpoints of their top and bottom edges.  The two cells covering the
        // poles extend down to +/-35.26 degrees at their vertices.  The maximum
        // error in this calculation is 0.5 * DBL_EPSILON.
        const PI_4: f64 = PI / 4.;
        let bound = match self.face {
            0 => s2::rect::Rect {
                lat: r1::interval::Interval::new(-PI_4, PI_4),
                lng: s1::Interval::new(-PI_4, PI_4),
            },
            1 => s2::rect::Rect {
                lat: r1::interval::Interval::new(-PI_4, PI_4),
                lng: s1::Interval::new(PI_4, 3. * PI_4),
            },
            2 => s2::rect::Rect {
                lat: r1::interval::Interval::new(*POLE_MIN_LAT, PI / 2.),
                lng: s1::interval::FULL,
            },
            3 => s2::rect::Rect {
                lat: r1::interval::Interval::new(-PI_4, PI_4),
                lng: s1::Interval::new(3. * PI_4, -3. * PI_4),
            },
            4 => s2::rect::Rect {
                lat: r1::interval::Interval::new(-PI_4, PI_4),
                lng: s1::Interval::new(-3. * PI_4, -PI_4),
            },
            5 => s2::rect::Rect {
                lat: r1::interval::Interval::new(-PI / 2., -1. * (*POLE_MIN_LAT)),
                lng: s1::interval::FULL,
            },
            _ => panic!("invalid face"),
        };

        // Finally, we expand the bound to account for the error when a point P is
        // converted to an LatLng to test for containment. (The bound should be
        // large enough so that it contains the computed LatLng of any contained
        // point, not just the infinite-precision version.) We don't need to expand
        // longitude because longitude is calculated via a single call to math.Atan2,
        // which is guaranteed to be semi-monotoniself.
        bound.expanded(&LatLng {
            lat: Rad(DBL_EPSILON).into(),
            lng: Rad(0.).into(),
        })
    }

    // ContainsPoint reports whether this cell contains the given point. Note that
    // unlike loop/Polygon, a Cell is considered to be a closed set. This means
    // that a point on a Cell's edge or vertex belong to the Cell and the relevant
    // adjacent Cells too.
    //
    // If you want every point to be contained by exactly one Cell,
    // you will need to convert the Cell to a loop.
    pub fn contains_point(&self, p: &Point) -> bool {
        if let Some((u, v)) = face_xyz_to_uv(self.face, p) {
            let uv = r2::point::Point { x: u, y: v };

            // Expand the (u,v) bound to ensure that
            //
            //   CellFromPoint(p).ContainsPoint(p)
            //
            // is always true. To do this, we need to account for the error when
            // converting from (u,v) coordinates to (s,t) coordinates. In the
            // normal case the total error is at most DBL_EPSILON.
            self.uv.expanded_by_margin(DBL_EPSILON).contains_point(&uv)
        } else {
            false
        }
    }
}

impl Region for Cell {
    /// cap_bound returns the bounding cap of this cell.
    fn cap_bound(&self) -> Cap {
        // We use the cell center in (u,v)-space as the cap axis.  This vector is very close
        // to GetCenter() and faster to compute.  Neither one of these vectors yields the
        // bounding cap with minimal surface area, but they are both pretty close.
        let center = self.uv.center();
        let v: Point = Point(face_uv_to_xyz(self.face, center.x, center.y).normalize());
        let mut cap = Cap::from(&v);

        let vertices = self.vertices();
        for vert in &vertices {
            cap = cap + vert;
        }
        cap
    }

    /// intersects_cell reports whether the intersection of this cell and the other cell is not nil.
    fn intersects_cell(&self, other: &Cell) -> bool {
        self.id.intersects(&other.id)
    }

    /// contains_cell reports whether this cell contains the other cell.
    fn contains_cell(&self, other: &Cell) -> bool {
        self.id.contains(&other.id)
    }
}

// BUG(roberts): Differences from C++:
// Subdivide
// BoundUV
// Distance/DistanceToEdge
// VertexChordDistance
// */
#[cfg(test)]
mod tests {
    extern crate rand;

    use super::*;
    use rand::Rng;
    use std;

    use crate::s2::random;

    // maxCellSize is the upper bounds on the number of bytes we want the Cell object to ever be.
    const MAX_CELL_SIZE: usize = 48;

    #[test]
    fn test_cell_object_size() {
        assert!(std::mem::size_of::<Cell>() <= MAX_CELL_SIZE);
    }

    /*
    use std::collections::{btree_map, BTreeMap};
    fn incr<K>(m: &mut BTreeMap<K, usize>, k: K)
        where K: std::cmp::Ord
    {
        match m.entry(k) {
            btree_map::Entry::Occupied(mut e) => {
                let item = e.get_mut();
                *item = *item + 1;
            }
            btree_map::Entry::Vacant(e) => {
                e.insert(1);
            }
        };
    }
    */

    //XXX
    #[test]
    #[ignore]
    fn test_cell_faces() {
        for face in 0..6 {
            let id = CellID::from_face(face);
            let cell = Cell::from(&id);

            assert_eq!(cell.id, id);
            assert_eq!(cell.face as u64, face);
            assert_eq!(cell.level, 0);
            assert_eq!(cell.orientation, cell.face & SWAP_MASK);

            assert_eq!(false, cell.is_leaf());

            let verts = cell.vertices();
            for k in 0..4 {
                let edge = cell.edge(k);
                let vert = &verts[k];
                let vert_cross = &verts[(k + 1) & 3];
                /*
                incr(&mut edge_counts, edge);
                incr(&mut vert_counts, vert);
                */

                assert_f64_eq!(0., vert.0.dot(&edge.0));
                assert_f64_eq!(0., vert_cross.0.dot(&edge.0));
                assert_f64_eq!(1., vert.0.cross(&vert_cross.0).normalize().dot(&edge.0));
            }
        }
        /*
        // Check that edges have multiplicity 2 and vertices have multiplicity 3.
        for k, v := range edgeCounts {
            if v != 2 {
                t.Errorf("edge %v counts wrong, got %d, want 2", k, v)
            }
        }
        for k, v := range vertexCounts {
            if v != 3 {
                t.Errorf("vertex %v counts wrong, got %d, want 3", k, v)
            }
        }
        */
    }

    fn test_cell_children_case(cell: &Cell) {
        if cell.is_leaf() {
            assert!(cell.children().is_none());
            return;
        }

        let children = cell.children().expect("no children for non-leaf cell");
        let mut child_id = cell.id.child_begin();
        for (i, child) in children.iter().enumerate() {
            assert_eq!(child_id, child.id);

            let direct = Cell::from(&child.id);
            assert_eq!(direct.face, child.face);
            assert_eq!(direct.level, child.level);
            assert_eq!(direct.orientation, child.orientation);
            assert_eq!(true, direct.center().approx_eq(&child.center()));

            let direct_verts = direct.vertices();
            let child_verts = child.vertices();

            for k in 0..4 {
                assert!(direct_verts[k].0.approx_eq(&child_verts[k].0));
                assert_eq!(direct.edge(k), child.edge(k));
            }

            assert_eq!(true, cell.contains_cell(&child));
            assert_eq!(true, cell.intersects_cell(&child));
            assert_eq!(false, child.contains_cell(&cell));
            assert_eq!(true, child.intersects_cell(&cell));

            for j in 0..4 {
                assert_eq!(true, cell.contains_point(&child_verts[j]));
                if j != i {
                    assert_eq!(false, child.contains_point(&children[j].center()));
                    assert_eq!(false, child.intersects_cell(&children[j]));
                }
            }

            let parent_cap = cell.cap_bound();
            let parent_rect = cell.rect_bound();

            if cell.contains_point(&Point::from_coords(0., 0., 1.))
                || cell.contains_point(&Point::from_coords(0., 0., -1.))
            {
                assert_eq!(true, parent_rect.lng.is_full());
            }

            let child_cap = child.cap_bound();
            let child_rect = child.rect_bound();
            let child_center = child.center();

            assert_eq!(true, child_cap.contains_point(&child_center));
            assert_eq!(
                true,
                child_rect.contains_point(&child_center),
                "child_rect {:?}.contains_point({:?}.center()) = false, want true",
                child_rect,
                child
            );
            assert_eq!(true, parent_cap.contains_point(&child_center));
            assert_eq!(true, parent_rect.contains_point(&child_center));

            for j in 0..4 {
                let v = &child_verts[j];
                assert_eq!(true, child_cap.contains_point(&v));
                assert_eq!(true, child_rect.contains_point(&v));
                assert_eq!(true, parent_cap.contains_point(&v));
                assert_eq!(true, parent_rect.contains_point(&v));

                if j != i {
                    // The bounding caps and rectangles should be tight enough so that
                    // they exclude at least two vertices of each adjacent cell.
                    let mut cap_count = 0;
                    let mut rect_count = 0;
                    let verts = children[j].vertices();

                    for k in 0..4 {
                        if child_cap.contains_point(&verts[k]) {
                            cap_count += 1;
                        }
                        if child_rect.contains_point(&verts[k]) {
                            rect_count += 1;
                        }
                    }
                    assert!(cap_count < 3);
                    if child_rect.lat.lo > PI / 2. && child_rect.lat.hi < PI / 2. {
                        assert!(rect_count < 3);
                    }
                }
            }

            // Check all children for the first few levels, and then sample randomly.
            // We also always subdivide the cells containing a few chosen points so
            // that we have a better chance of sampling the minimum and maximum metric
            // values.  kMaxSizeUV is the absolute value of the u- and v-coordinate
            // where the cell size at a given level is maximal.
            let max_size_uv = 0.3964182625366691;
            let special_uv = [
                r2::point::Point::new(DBL_EPSILON, DBL_EPSILON), // Face center
                r2::point::Point::new(DBL_EPSILON, 1.),          // Edge midpoint
                r2::point::Point::new(1., 1.),                   // Face corner
                r2::point::Point::new(max_size_uv, max_size_uv), // Largest cell area
                r2::point::Point::new(DBL_EPSILON, max_size_uv), // Longest edge/diagonal
            ];

            let mut force_subdivide = false;
            for uv in special_uv.iter() {
                if child.bound_uv().contains_point(uv) {
                    force_subdivide = true;
                }
            }

            // For a more in depth test, add an "|| oneIn(n)" to this condition
            // to cause more children to be tested beyond the ones to level 5.
            if force_subdivide || cell.level < 5 {
                test_cell_children_case(child);
            }

            child_id = child_id.next();
        }
    }

    #[test]
    fn test_cell_children() {
        test_cell_children_case(&Cell::from(CellID::from_face(0)));
        test_cell_children_case(&Cell::from(CellID::from_face(3)));
        test_cell_children_case(&Cell::from(CellID::from_face(5)));
    }

    #[test]
    fn test_cell_areas() {
        // relative error bounds for each type of area computation
        let exact_error = (1. + 1e-6f64).ln();
        let approx_error = (1.03f64).ln();
        let avg_error = (1. + 1e-15f64).ln();

        // Test 1. Check the area of a top level cell.
        let level1_cell = CellID(0x1000000000000000);
        let want_area = 4. * PI / 6.;

        assert_f64_eq!(Cell::from(&level1_cell).exact_area(), want_area);

        // Test 2. Iterate inwards from this cell, checking at every level that
        // the sum of the areas of the children is equal to the area of the parent.
        let mut child_index = 1;
        let mut ci = CellID(0x1000000000000000);
        while ci.level() < 21 {
            let mut exact_area = 0.;
            let mut approx_area = 0.;
            let mut avg_area = 0.;

            for child in ci.children().iter() {
                exact_area += Cell::from(child).exact_area();
                approx_area += Cell::from(child).approx_area();
                avg_area += Cell::from(child).average_area();
            }

            let cell = Cell::from(&ci);

            assert_f64_eq!(exact_area, cell.exact_area());

            child_index = (child_index + 1) % 4;

            // For exact_area(), the best relative error we can expect is about 1e-6
            // because the precision of the unit vector coordinates is only about 1e-15
            // and the edge length of a leaf cell is about 1e-9.
            assert!((exact_area / cell.exact_area()).ln().abs() < exact_error);

            // For ApproxArea(), the areas are accurate to within a few percent.
            assert!((approx_area / cell.approx_area()).ln().abs() < approx_error);

            // For AverageArea(), the areas themselves are not very accurate, but
            // the average area of a parent is exactly 4 times the area of a child.
            assert!((avg_area / cell.average_area()).ln().abs() < avg_error);

            ci = ci.children()[child_index].clone();
        }
    }

    fn test_cell_intersects_cell_case(a: CellID, b: CellID, want: bool) {
        assert_eq!(want, Cell::from(a).intersects_cell(&Cell::from(b)));
    }

    #[test]
    fn test_cell_intersects_cell() {
        test_cell_intersects_cell_case(
            CellID::from_face(0).child_begin_at_level(2),
            CellID::from_face(0).child_begin_at_level(2),
            true,
        );

        test_cell_intersects_cell_case(
            CellID::from_face(0).child_begin_at_level(2),
            CellID::from_face(0)
                .child_begin_at_level(2)
                .child_begin_at_level(5),
            true,
        );

        test_cell_intersects_cell_case(
            CellID::from_face(0).child_begin_at_level(2),
            CellID::from_face(0).child_begin_at_level(2).next(),
            false,
        );

        test_cell_intersects_cell_case(
            CellID::from_face(0).child_begin_at_level(2).next(),
            CellID::from_face(0).child_begin_at_level(2),
            false,
        );
    }

    fn test_cell_rect_bound_case(lat: f64, lng: f64) {
        let c = Cell::from(LatLng::new(Deg(lat).into(), Deg(lng).into()));
        let rect = c.rect_bound();
        let verts = c.vertices();
        for i in 0..4 {
            assert!(rect.contains_latlng(&LatLng::from(&verts[i])));
        }
    }

    #[test]
    fn test_cell_rect_bound() {
        test_cell_rect_bound_case(50., 50.);
        test_cell_rect_bound_case(-50., 50.);
        test_cell_rect_bound_case(50., -50.);
        test_cell_rect_bound_case(-50., -50.);
        test_cell_rect_bound_case(0., 0.);
        test_cell_rect_bound_case(0., 180.);
        test_cell_rect_bound_case(0., -179.);
    }

    #[test]
    fn test_cell_cap_bound() {
        let c = Cell::from(CellID::from_face(0).child_begin_at_level(20));
        let s2_cap = c.cap_bound();

        let verts = c.vertices();
        for i in 0..4 {
            assert!(s2_cap.contains_point(&verts[i]));
        }
    }

    fn test_cell_contains_point_case(a: &Cell, b: &Point, want: bool) {
        assert_eq!(want, a.contains_point(b));
    }

    #[test]
    fn test_cell_contains_point() {
        let id = CellID::from_face(0);

        test_cell_contains_point_case(
            &Cell::from(id.child_begin_at_level(2)),
            &Cell::from(id.child_begin_at_level(2).child_begin_at_level(5)).vertices()[1],
            true,
        );

        test_cell_contains_point_case(
            &Cell::from(id.child_begin_at_level(2)),
            &Cell::from(id.child_begin_at_level(2)).vertices()[1],
            true,
        );

        test_cell_contains_point_case(
            &Cell::from(id.child_begin_at_level(2).child_begin_at_level(5)),
            &Cell::from(id.child_begin_at_level(2).next().child_begin_at_level(5)).vertices()[1],
            false,
        );
    }

    use crate::s2::edgeutil;

    #[test]
    fn test_cell_contains_point_consistent_will_s2_cellid_from_point() {
        // Construct many points that are nearly on a Cell edge, and verify that
        // CellFromCellID(cellIDFromPoint(p)).Contains(p) is always true.
        let mut rng = random::rng();

        for _ in 0..1000 {
            let cell = Cell::from(&random::cellid(&mut rng));
            let i1 = rng.gen_range(0, 4);
            let i2 = (i1 + 1) & 3;
            let v1 = &cell.vertices()[i1];

            let v2 = random::sample_point_from_cap(
                &mut rng,
                Cap::from_center_angle(&cell.vertex(i2), &Angle::from(Rad(EPSILON))),
            );
            let p = edgeutil::interpolate(rng.gen_range(0., 1.), &v1, &v2);

            assert!(Cell::from(&CellID::from(&p)).contains_point(&p));
        }
    }

    #[test]
    fn test_cell_contains_point_contains_ambiguous_point() {
        // This tests a case where S2CellId returns the "wrong" cell for a point
        // that is very close to the cell edge. (ConsistentWithS2CellIdFromPoint
        // generates more examples like this.)
        //
        // The Point below should have x = 0, but conversion from LatLng to
        // (x,y,z) gives x = ~6.1e-17. When xyz is converted to uv, this gives
        // u = -6.1e-17. However when converting to st, which has a range of [0,1],
        // the low precision bits of u are lost and we wind up with s = 0.5.
        // cellIDFromPoint then chooses an arbitrary neighboring cell.
        //
        // This tests that Cell.ContainsPoint() expands the cell bounds sufficiently
        // so that the returned cell is still considered to contain p.
        let p = Point::from(LatLng::new(Deg(-2.).into(), Deg(90.).into()));
        let cell = Cell::from(CellID::from(&p).parent(1));
        assert_eq!(true, cell.contains_point(&p));
    }
}
