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

use crate::r1::interval::{self, Interval};
use crate::r2::point::Point;

/// Rect represents a closed axis-aligned rectangle in the (x,y) plane.
#[derive(Clone, Debug, Default, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Rect {
    /// x interval of the rect
    pub x: Interval,
    /// y interval of the rect
    pub y: Interval,
}

/// Canonical empty rectangle. Use IsEmpty() to test
/// for empty rectangles, since they have more than one representation. A Rect::default()
/// is not the same as the EmptyRect.
pub const EMPTY: Rect = Rect {
    x: interval::EMPTY,
    y: interval::EMPTY,
};

impl Rect {
    /// from_points constructs a rect that contains the given points.
    pub fn from_points(points: &[Point]) -> Self {
        // Because the default value on interval is 0,0, we need to manually
        // define the interval from the first point passed in as our starting
        // interval, otherwise we end up with the case of passing in
        // Point{0.2, 0.3} and getting the starting Rect of {0, 0.2}, {0, 0.3}
        // instead of the Rect {0.2, 0.2}, {0.3, 0.3} which is not correct.
        if points.is_empty() {
            return Self::default();
        }

        let mut r = Rect {
            x: Interval::from_point(points[0].x),
            y: Interval::from_point(points[0].y),
        };
        for p in &points[1..] {
            r = r + p;
        }
        r
    }

    /// from_center_size constructs a rectangle with the given center and size.
    /// Both dimensions of size must be non-negative.
    pub fn from_center_size(center: &Point, size: &Point) -> Self {
        Rect {
            x: Interval::from_point(center.x).expanded(size.x / 2.),
            y: Interval::from_point(center.y).expanded(size.y / 2.),
        }
    }

    /// is_valid reports whether the rectangle is valid.
    /// This requires the width to be empty iff the height is empty.
    pub fn is_valid(&self) -> bool {
        self.x.is_empty() == self.y.is_empty()
    }

    /// is_empty reports whether the rectangle is empty.
    pub fn is_empty(&self) -> bool {
        self.x.is_empty()
    }

    /// vertices returns all four vertices of the rectangle. Vertices are returned in
    /// CCW direction starting with the lower left corner.
    pub fn vertices(&self) -> [Point; 4] {
        [
            Point::new(self.x.lo, self.y.lo),
            Point::new(self.x.hi, self.y.lo),
            Point::new(self.x.hi, self.y.hi),
            Point::new(self.x.lo, self.y.hi),
        ]
    }

    /// vertex_ij returns the vertex in direction i along the X-axis (0=left, 1=right) and
    /// direction j along the Y-axis (0=down, 1=up).
    pub fn vertex_ij(&self, i: isize, j: isize) -> Point {
        let x = if i == 0 { self.x.lo } else { self.x.hi };
        let y = if j == 0 { self.y.lo } else { self.y.hi };
        Point::new(x, y)
    }

    /// lo returns the low corner of the rect.
    pub fn lo(&self) -> Point {
        Point::new(self.x.lo, self.y.lo)
    }

    /// hi returns the high corner of the rect.
    pub fn hi(&self) -> Point {
        Point::new(self.x.hi, self.y.hi)
    }

    /// center returns the center of the rectangle in (x,y)-space
    pub fn center(&self) -> Point {
        Point::new(self.x.center(), self.y.center())
    }

    /// size returns the width and height of this rectangle in (x,y)-space. Empty
    /// rectangles have a negative width and height.
    pub fn size(&self) -> Point {
        Point::new(self.x.len(), self.y.len())
    }

    /// contains_point reports whether the rectangle contains the given point.
    /// Rectangles are closed regions, i.e. they contain their boundary.
    pub fn contains_point(&self, p: &Point) -> bool {
        self.x.contains(p.x) && self.y.contains(p.y)
    }

    /// interior_contains_point returns true iff the given point is contained in the interior
    /// of the region (i.e. the region excluding its boundary).
    pub fn interior_contains_point(&self, p: &Point) -> bool {
        self.x.interior_contains(p.x) && self.y.interior_contains(p.y)
    }

    /// contains reports whether the rectangle contains the given rectangle.
    pub fn contains(&self, r: &Self) -> bool {
        self.x.contains_interval(&r.x) && self.y.contains_interval(&r.y)
    }

    /// interior_contains reports whether the interior of this rectangle contains all of the
    /// points of the given other rectangle (including its boundary).
    pub fn interior_contains(&self, r: &Self) -> bool {
        self.x.interior_contains_interval(&r.x) && self.y.interior_contains_interval(&r.y)
    }

    /// intersects reports whether this rectangle and the other rectangle have any points in common.
    pub fn intersects(&self, r: &Self) -> bool {
        self.x.intersects(&r.x) && self.y.intersects(&r.y)
    }

    /// interior_intersects reports whether the interior of this rectangle intersects
    /// any point (including the boundary) of the given other rectangle.
    pub fn interior_intersects(&self, r: &Self) -> bool {
        self.x.interior_intersects(&r.x) && self.y.interior_intersects(&r.y)
    }

    /// clamp_point returns the closest point in the rectangle to the given point.
    /// The rectangle must be non-empty.
    pub fn clamp_point(&self, p: &Point) -> Point {
        Point::new(self.x.clamp_point(p.x), self.y.clamp_point(p.y))
    }

    /// expanded returns a rectangle that has been expanded in the x-direction
    /// by margin.X, and in y-direction by margin.Y. If either margin is empty,
    /// then shrink the interval on the corresponding sides instead. The resulting
    /// rectangle may be empty. Any expansion of an empty rectangle remains empty.
    pub fn expanded(&self, margin: &Point) -> Self {
        let x = self.x.expanded(margin.x);
        let y = self.y.expanded(margin.y);
        if x.is_empty() || y.is_empty() {
            EMPTY
        } else {
            Rect { x, y }
        }
    }

    /// expanded_by_margin returns a Rect that has been expanded by the amount on all sides.
    pub fn expanded_by_margin(&self, margin: f64) -> Self {
        self.expanded(&Point::new(margin, margin))
    }

    /// union returns the smallest rectangle containing the union of this rectangle and
    /// the given rectangle.
    pub fn union(&self, other: &Self) -> Self {
        Rect {
            x: self.x.union(&other.x),
            y: self.y.union(&other.y),
        }
    }

    /// intersection returns the smallest rectangle containing the intersection of this
    /// rectangle and the given rectangle.
    pub fn intersection(&self, other: &Self) -> Self {
        let x = self.x.intersection(&other.x);
        let y = self.y.intersection(&other.y);
        if x.is_empty() || y.is_empty() {
            EMPTY
        } else {
            Rect { x, y }
        }
    }

    /// approx_equals returns true if the x- and y-intervals of the two rectangles are
    /// the same up to the given tolerance.
    pub fn approx_eq(&self, other: &Self) -> bool {
        self.x.approx_eq(&other.x) && self.y.approx_eq(&other.y)
    }
}

impl<'b> std::ops::Add<&'b Point> for Rect {
    type Output = Self;
    /// expands the rectangle to include the given point. The rectangle is
    /// expanded by the minimum amount possible.
    fn add(self, p: &'b Point) -> Self::Output {
        Self::Output {
            x: self.x + p.x,
            y: self.y + p.y,
        }
    }
}

impl<'b> std::ops::Add<&'b Rect> for Rect {
    type Output = Self;
    /// expands the rectangle to include the given rectangle. This is the
    /// same as replacing the rectangle by the union of the two rectangles, but
    /// is more efficient.
    fn add(self, p: &'b Rect) -> Self::Output {
        Self::Output {
            x: self.x.union(&p.x),
            y: self.y.union(&p.y),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SW: Point = Point { x: 0., y: 0.25 };
    const SE: Point = Point { x: 0.5, y: 0.25 };
    const NE: Point = Point { x: 0.5, y: 0.75 };
    const NW: Point = Point { x: 0., y: 0.75 };

    const RECT: Rect = Rect {
        x: Interval { lo: 0., hi: 0.5 },
        y: Interval { lo: 0.25, hi: 0.75 },
    };

    const RECT_MID: Rect = Rect {
        x: Interval { lo: 0.25, hi: 0.25 },
        y: Interval { lo: 0.5, hi: 0.5 },
    };

    const RECT_SW: Rect = Rect {
        x: Interval { lo: SW.x, hi: SW.x },
        y: Interval { lo: SW.y, hi: SW.y },
    };

    const RECT_NE: Rect = Rect {
        x: Interval { lo: NE.x, hi: NE.x },
        y: Interval { lo: NE.y, hi: NE.y },
    };

    use crate::r2::point::Point;

    #[test]
    fn empty_rect() {
        assert!(EMPTY.is_valid());
        assert!(EMPTY.is_empty());
    }

    #[test]
    fn test_from_various_types() {
        let d1 = Rect::from_points(&[Point::new(0.1, 0.), Point::new(0.25, 0.1)]);

        assert!(
            Rect::from_center_size(&Point::new(0.3, 0.5), &Point::new(0.2, 0.4)).approx_eq(
                &Rect::from_points(&[Point::new(0.2, 0.3), Point::new(0.4, 0.7)])
            )
        );

        assert!(
            Rect::from_center_size(&Point::new(1., 0.1), &Point::new(0., 2.)).approx_eq(
                &Rect::from_points(&[Point::new(1., -0.9), Point::new(1., 1.1)])
            )
        );

        assert!(d1.approx_eq(&Rect { x: d1.x, y: d1.y }));

        assert!(
            Rect::from_points(&[Point::new(0.15, 0.3), Point::new(0.35, 0.9)]).approx_eq(
                &Rect::from_points(&[Point::new(0.15, 0.9), Point::new(0.35, 0.3)])
            )
        );

        assert!(
            Rect::from_points(&[Point::new(0.12, 0.), Point::new(0.83, 0.5)]).approx_eq(
                &Rect::from_points(&[Point::new(0.83, 0.), Point::new(0.12, 0.5)])
            )
        );
    }

    #[test]
    fn test_center() {
        assert!(EMPTY.center().approx_eq(&Point::new(0.5, 0.5)));
        assert!(RECT.center().approx_eq(&Point::new(0.25, 0.5)));
    }

    #[test]
    fn test_vertices() {
        let want = &[SW, SE, NE, NW];
        assert_eq!(&RECT.vertices(), want);
    }

    #[test]
    fn test_contains_point() {
        assert_eq!(true, RECT.contains_point(&Point::new(0.2, 0.4)));
        assert_eq!(false, RECT.contains_point(&Point::new(0.2, 0.8)));
        assert_eq!(false, RECT.contains_point(&Point::new(-0.1, 0.4)));
        assert_eq!(false, RECT.contains_point(&Point::new(0.6, 0.1)));
        assert_eq!(true, RECT.contains_point(&Point::new(RECT.x.lo, RECT.y.lo)));
        assert_eq!(true, RECT.contains_point(&Point::new(RECT.x.hi, RECT.y.hi)));
    }

    #[test]
    fn test_interior_contains_point() {
        // Check corners are not contained.
        assert_eq!(false, RECT.interior_contains_point(&SW));
        assert_eq!(false, RECT.interior_contains_point(&NE));
        // Check a point on the border is not contained.
        assert_eq!(false, RECT.interior_contains_point(&Point::new(0., 0.5)));
        assert_eq!(false, RECT.interior_contains_point(&Point::new(0.25, 0.25)));
        assert_eq!(false, RECT.interior_contains_point(&Point::new(0.5, 0.5)));
        // Check points inside are contained.
        assert_eq!(true, RECT.interior_contains_point(&Point::new(0.125, 0.6)));
    }

    fn test_interval_cases(
        r1: &Rect,
        r2: &Rect,
        contains: bool,
        int_contains: bool,
        intersects: bool,
        int_intersects: bool,
        want_union: &Rect,
        want_intersection: &Rect,
    ) {
        assert_eq!(contains, r1.contains(r2));
        assert_eq!(int_contains, r1.interior_contains(r2));
        assert_eq!(intersects, r1.intersects(r2));
        assert_eq!(int_intersects, r1.interior_intersects(r2));

        assert!(r1.union(r2).approx_eq(&want_union));
        assert!(r1.intersection(r2).approx_eq(&want_intersection));

        assert!((r1.clone() + r2).approx_eq(&want_union));
    }

    #[test]
    fn test_interval_ops() {
        test_interval_cases(&RECT, &RECT_MID, true, true, true, true, &RECT, &RECT_MID);
        test_interval_cases(&RECT, &RECT_SW, true, false, true, false, &RECT, &RECT_SW);
        test_interval_cases(&RECT, &RECT_NE, true, false, true, false, &RECT, &RECT_NE);

        test_interval_cases(
            &RECT,
            &Rect::from_points(&[Point::new(0.45, 0.1), Point::new(0.75, 0.3)]),
            false,
            false,
            true,
            true,
            &Rect::from_points(&[Point::new(0., 0.1), Point::new(0.75, 0.75)]),
            &Rect::from_points(&[Point::new(0.45, 0.25), Point::new(0.5, 0.3)]),
        );

        test_interval_cases(
            &RECT,
            &Rect::from_points(&[Point::new(0.5, 0.1), Point::new(0.7, 0.3)]),
            false,
            false,
            true,
            false,
            &Rect::from_points(&[Point::new(0., 0.1), Point::new(0.7, 0.75)]),
            &Rect::from_points(&[Point::new(0.5, 0.25), Point::new(0.5, 0.3)]),
        );

        test_interval_cases(
            &RECT,
            &Rect::from_points(&[Point::new(0.45, 0.1), Point::new(0.7, 0.25)]),
            false,
            false,
            true,
            false,
            &Rect::from_points(&[Point::new(0., 0.1), Point::new(0.7, 0.75)]),
            &Rect::from_points(&[Point::new(0.45, 0.25), Point::new(0.5, 0.25)]),
        );

        test_interval_cases(
            &Rect::from_points(&[Point::new(0.1, 0.2), Point::new(0.1, 0.3)]),
            &Rect::from_points(&[Point::new(0.15, 0.7), Point::new(0.2, 0.8)]),
            false,
            false,
            false,
            false,
            &Rect::from_points(&[Point::new(0.1, 0.2), Point::new(0.2, 0.8)]),
            &EMPTY,
        );

        // Check that the intersection of two rectangles that overlap in x but not y
        // is valid, and vice versa.
        test_interval_cases(
            &Rect::from_points(&[Point::new(0.1, 0.2), Point::new(0.4, 0.5)]),
            &Rect::from_points(&[Point::new(0., 0.), Point::new(0.2, 0.1)]),
            false,
            false,
            false,
            false,
            &Rect::from_points(&[Point::new(0., 0.), Point::new(0.4, 0.5)]),
            &EMPTY,
        );

        test_interval_cases(
            &Rect::from_points(&[Point::new(0., 0.), Point::new(0.1, 0.3)]),
            &Rect::from_points(&[Point::new(0.2, 0.1), Point::new(0.3, 0.4)]),
            false,
            false,
            false,
            false,
            &Rect::from_points(&[Point::new(0., 0.), Point::new(0.3, 0.4)]),
            &EMPTY,
        );
    }

    #[test]
    fn test_add_point() {
        let r1 = RECT.clone();
        let mut r2 = EMPTY.clone();

        r2 = r2 + &SW;
        r2 = r2 + &SE;
        r2 = r2 + &NW;
        r2 = r2 + &Point::new(0.1, 0.4);

        assert!(r1.approx_eq(&r2));
    }

    fn test_clamp_cases(r: &Rect, p: &Point, want: &Point) {
        assert_eq!(want, &r.clamp_point(p));
    }

    #[test]
    fn test_clamp_point() {
        let r = Rect {
            x: Interval::new(0., 0.5),
            y: Interval::new(0.25, 0.75),
        };

        test_clamp_cases(&r, &Point::new(-0.01, 0.24), &Point::new(0., 0.25));
        test_clamp_cases(&r, &Point::new(-5.0, 0.48), &Point::new(0., 0.48));
        test_clamp_cases(&r, &Point::new(-5.0, 2.48), &Point::new(0., 0.75));
        test_clamp_cases(&r, &Point::new(0.17, 2.48), &Point::new(0.17, 0.75));

        test_clamp_cases(&r, &Point::new(6.19, 2.48), &Point::new(0.5, 0.75));
        test_clamp_cases(&r, &Point::new(6.19, 0.53), &Point::new(0.5, 0.53));
        test_clamp_cases(&r, &Point::new(6.19, -2.53), &Point::new(0.5, 0.25));
        test_clamp_cases(&r, &Point::new(0.33, 2.48), &Point::new(0.33, 0.75));
        test_clamp_cases(&r, &Point::new(0.33, 0.37), &Point::new(0.33, 0.37));
    }

    #[test]
    fn test_expanded_empty() {
        assert!(EMPTY.expanded(&Point::new(0.1, 0.3)).is_empty());
        assert!(EMPTY.expanded(&Point::new(-0.1, -0.3)).is_empty());
        assert!(EMPTY.expanded(&Point::new(-0.1, 0.3)).is_empty());
        assert!(EMPTY.expanded(&Point::new(0.1, -0.2)).is_empty());
    }

    #[test]
    fn test_expanded_equals() {
        assert!(
            Rect::from_points(&[Point::new(0.2, 0.4), Point::new(0.3, 0.7)])
                .expanded(&Point::new(0.1, 0.3))
                .approx_eq(&Rect::from_points(&[
                    Point::new(0.1, 0.1),
                    Point::new(0.4, 1.0)
                ]))
        );

        assert!(
            Rect::from_points(&[Point::new(0.2, 0.4), Point::new(0.3, 0.7)])
                .expanded(&Point::new(0.1, -0.1))
                .approx_eq(&Rect::from_points(&[
                    Point::new(0.1, 0.5),
                    Point::new(0.4, 0.6)
                ]))
        );

        assert!(
            Rect::from_points(&[Point::new(0.2, 0.4), Point::new(0.3, 0.7)])
                .expanded(&Point::new(0.1, 0.1))
                .approx_eq(&Rect::from_points(&[
                    Point::new(0.1, 0.3),
                    Point::new(0.4, 0.8)
                ]))
        );
    }
}
