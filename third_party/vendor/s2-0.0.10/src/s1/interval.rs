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

/// Interval represents a closed interval on a unit circle.
/// Zero-length intervals (where Lo == Hi) represent single points.
/// If Lo > Hi then the interval is "inverted".
/// The point at (-1, 0) on the unit circle has two valid representations,
/// [π,π] and [-π,-π]. We normalize the latter to the former in Interval::new.
/// There are two special intervals that take advantage of that:
///   - the full interval, [-π,π], and
///   - the empty interval, [π,-π].
/// Treat the exported fields as read-only.
#[derive(Clone, Copy, PartialEq, Default)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Interval {
    pub lo: f64,
    pub hi: f64,
}
impl std::fmt::Debug for Interval {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "[{:.7}, {:.7}]", self.lo, self.hi)
    }
}

/// an empty interval.
pub const EMPTY: Interval = Interval { lo: PI, hi: -PI };
/// a full interval.
pub const FULL: Interval = Interval { lo: -PI, hi: PI };

/// Compute distance from a to b in [0,2π], in a numerically stable way.
fn positive_distance(a: f64, b: f64) -> f64 {
    let d = b - a;
    if d >= 0. {
        d
    } else {
        (b + PI) - (a - PI)
    }
}

impl Interval {
    /// from_endpoint constructs a new interval from endpoints.
    /// Both arguments must be in the range [-π,π]. This function allows inverted intervals
    /// to be created.
    pub fn new(lo: f64, hi: f64) -> Self {
        let mut i = Interval { lo, hi };
        if lo == -PI && hi != PI {
            i.lo = PI
        }
        if hi == -PI && lo != PI {
            i.hi = PI
        }
        i
    }

    /// from_point_pair returns the minimal interval containing the two given points.
    /// Both arguments must be in [-π,π].
    pub fn from_point_pair(mut a: f64, mut b: f64) -> Self {
        if a == -PI {
            a = PI
        }
        if b == -PI {
            b = PI
        }
        if positive_distance(a, b) <= PI {
            Interval { lo: a, hi: b }
        } else {
            Interval { lo: b, hi: a }
        }
    }

    /// is_valid reports whether the interval is valid.
    pub fn is_valid(&self) -> bool {
        self.lo.abs() <= PI
            && self.hi.abs() <= PI
            && !(self.lo == -PI && self.hi != PI)
            && !(self.hi == -PI && self.lo != PI)
    }

    /// is_full reports whether the interval is full.
    pub fn is_full(&self) -> bool {
        *self == FULL
    }

    /// is_empty reports whether the interval is empty.
    pub fn is_empty(&self) -> bool {
        *self == EMPTY
    }

    /// is_inverted reports whether the interval is inverted; that is, whether Lo > Hi.
    pub fn is_inverted(&self) -> bool {
        self.lo > self.hi
    }

    /// invert returns the interval with endpoints swapped.
    pub fn invert(&self) -> Interval {
        Interval {
            lo: self.hi,
            hi: self.lo,
        }
    }

    /// center returns the midpoint of the interval.
    /// It is undefined for full and empty intervals.
    pub fn center(&self) -> f64 {
        let c = 0.5 * (self.lo + self.hi);
        if !self.is_inverted() {
            c
        } else if c <= 0. {
            c + PI
        } else {
            c - PI
        }
    }

    /// len returns the length of the interval.
    /// The length of an empty interval is negative.
    pub fn len(&self) -> f64 {
        let mut l = self.hi - self.lo;
        if l >= 0. {
            return l;
        }
        l += 2. * PI;
        if l > 0. {
            return l;
        }
        -1f64
    }

    /// fast_contains returns true iff the interval contains p.
    /// Assumes p ∈ (-π,π].
    pub fn fast_contains(&self, p: f64) -> bool {
        if self.is_inverted() {
            (p >= self.lo || p <= self.hi) && !self.is_empty()
        } else {
            p >= self.lo && p <= self.hi
        }
    }

    /// contains returns true iff the interval contains p.
    /// Assumes p ∈ [-π,π].
    pub fn contains(&self, mut p: f64) -> bool {
        if p == -PI {
            p = PI
        }
        self.fast_contains(p)
    }

    /// contains_interval returns true iff the interval contains oi.
    pub fn contains_interval(&self, other: &Self) -> bool {
        if self.is_inverted() {
            if other.is_inverted() {
                other.lo >= self.lo && other.hi <= self.hi
            } else {
                (other.lo >= self.lo || other.hi <= self.hi) && !self.is_empty()
            }
        } else if other.is_inverted() {
            self.is_full() || other.is_empty()
        } else {
            other.lo >= self.lo && other.hi <= self.hi
        }
    }

    /// interior_contains returns true iff the interior of the interval contains p.
    /// Assumes p ∈ [-π,π].
    pub fn interior_contains(&self, mut p: f64) -> bool {
        if p == -PI {
            p = PI
        }
        if self.is_inverted() {
            p > self.lo || p < self.hi
        } else {
            (p > self.lo && p < self.hi) || self.is_full()
        }
    }

    /// interior_contains_interval returns true iff the interior of the interval contains oi.
    pub fn interior_contains_interval(&self, other: &Self) -> bool {
        if self.is_inverted() {
            if other.is_inverted() {
                (other.lo > self.lo && other.hi < self.hi) || other.is_empty()
            } else {
                other.lo > self.lo || other.hi < self.hi
            }
        } else if other.is_inverted() {
            self.is_full() || other.is_empty()
        } else {
            (other.lo > self.lo && other.hi < self.hi) || self.is_full()
        }
    }

    /// intersects returns true iff the interval contains any points in common with oi.
    pub fn intersects(&self, other: &Self) -> bool {
        if self.is_empty() || other.is_empty() {
            false
        } else if self.is_inverted() {
            other.is_inverted() || other.lo <= self.hi || other.hi >= self.lo
        } else if other.is_inverted() {
            other.lo <= self.hi || other.hi >= self.lo
        } else {
            other.lo <= self.hi && other.hi >= self.lo
        }
    }

    /// interior_intersects returns true iff the interior of the interval contains any points in
    /// common with other, including the latter's boundary.
    pub fn interior_intersects(&self, other: &Self) -> bool {
        if self.is_empty() || other.is_empty() || self.lo == self.hi {
            false
        } else if self.is_inverted() {
            other.is_inverted() || other.lo < self.hi || other.hi > self.lo
        } else if other.is_inverted() {
            other.lo < self.hi || other.hi > self.lo
        } else {
            (other.lo < self.hi && other.hi > self.lo) || self.is_full()
        }
    }

    /// union returns the smallest interval that contains both the interval and oi.
    pub fn union(&self, other: &Self) -> Self {
        if other.is_empty() {
            *self
        } else if self.fast_contains(other.lo) {
            if self.fast_contains(other.hi) {
                // Either other⊂ i, or i ∪ other is the full interval.
                if self.contains_interval(other) {
                    *self
                } else {
                    FULL
                }
            } else {
                Interval {
                    lo: self.lo,
                    hi: other.hi,
                }
            }
        } else if self.fast_contains(other.hi) {
            Interval {
                lo: other.lo,
                hi: self.hi,
            }
        } else if self.is_empty() || other.fast_contains(self.lo) {
            // Neither endpoint of oi is in i. Either i ⊂ oi, or i and oi are disjoint.
            *other
        } else if positive_distance(other.hi, self.lo) < positive_distance(self.hi, other.lo) {
            // This is the only hard case where we need to find the closest pair of endpoints.
            Interval {
                lo: other.lo,
                hi: self.hi,
            }
        } else {
            Interval {
                lo: self.lo,
                hi: other.hi,
            }
        }
    }

    /// intersection returns the smallest interval that contains the intersection of the interval and oi.
    pub fn intersection(&self, other: &Self) -> Self {
        if other.is_empty() {
            return EMPTY;
        }

        if self.fast_contains(other.lo) {
            if self.fast_contains(other.hi) {
                // Either oi ⊂ i, or i and oi intersect twice. Neither are empty.
                // In the first case we want to return i (which is shorter than oi).
                // In the second case one of them is inverted, and the smallest interval
                // that covers the two disjoint pieces is the shorter of i and oi.
                // We thus want to pick the shorter of i and oi in both cases.
                if other.len() < self.len() {
                    *other
                } else {
                    *self
                }
            } else {
                Interval {
                    lo: other.lo,
                    hi: self.hi,
                }
            }
        } else if self.fast_contains(other.hi) {
            Interval {
                lo: self.lo,
                hi: other.hi,
            }
        } else if other.fast_contains(self.lo) {
            // Neither endpoint of oi is in i. Either i ⊂ oi, or i and oi are disjoint.
            *self
        } else {
            EMPTY
        }
    }

    /// Expanded returns an interval that has been expanded on each side by margin.
    /// If margin is negative, then the function shrinks the interval on
    /// each side by margin instead. The resulting interval may be empty or
    /// full. Any expansion (positive or negative) of a full interval remains
    /// full, and any expansion of an empty interval remains empty.
    pub fn expanded(&self, margin: f64) -> Self {
        if margin >= 0. {
            if self.is_empty() {
                return *self;
            }
            // Check whether this interval will be full after expansion, allowing
            // for a rounding error when computing each endpoint.
            if self.len() + 2. * margin + 2. * DBL_EPSILON >= 2. * PI {
                return FULL;
            }
        } else {
            if self.is_full() {
                return *self;
            }
            // Check whether this interval will be empty after expansion, allowing
            // for a rounding error when computing each endpoint.
            if self.len() + 2. * margin - 2. * DBL_EPSILON <= 0. {
                return EMPTY;
            }
        }
        let mut result = Interval::new(
            remainder(self.lo - margin, 2. * PI),
            remainder(self.hi + margin, 2. * PI),
        );
        if result.lo <= -PI {
            result.lo = PI
        }
        result
    }
}

impl std::ops::Add<f64> for Interval {
    type Output = Interval;
    fn add(self, p: f64) -> Self::Output {
        &self + p
    }
}
impl<'a> std::ops::Add<f64> for &'a Interval {
    type Output = Interval;
    /// add returns the interval expanded by the minimum amount necessary such
    /// that it contains the given point "p" (an angle in the range [-Pi, Pi]).
    fn add(self, mut p: f64) -> Self::Output {
        if p.abs() > PI {
            return *self;
        }

        if p == -PI {
            p = PI
        }
        if self.fast_contains(p) {
            return *self;
        }
        if self.is_empty() {
            return Interval { lo: p, hi: p };
        }
        if positive_distance(p, self.lo) < positive_distance(self.hi, p) {
            return Interval { lo: p, hi: self.hi };
        }
        Interval { lo: self.lo, hi: p }
    }
}

impl From<Interval> for r1::interval::Interval {
    fn from(i: Interval) -> Self {
        Self { lo: i.lo, hi: i.hi }
    }
}

impl From<r1::interval::Interval> for Interval {
    fn from(i: r1::interval::Interval) -> Self {
        Self { lo: i.lo, hi: i.hi }
    }
}

// BUG(dsymonds): The major differences from the C++ version are:
//   - no validity checking on construction, etc. (not a bug?)
//   - a few operations

#[cfg(test)]
#[allow(non_upper_case_globals)]
#[allow(dead_code)]
mod tests {
    use super::*;

    // Some standard intervals for use throughout the tests.
    lazy_static! {
        static ref full: Interval = FULL;
        static ref empty: Interval = EMPTY;
        // Single-point intervals:
        static ref zero: Interval = Interval::default();
        static ref pi2: Interval = Interval::new(PI/2., PI/2.);
        static ref pi: Interval = Interval::new(PI, PI);
        static ref mipi  :Interval = Interval::new(-PI, -PI); // same as pi after normalization
        static ref mipi2 :Interval = Interval::new(-PI/2., -PI/2.);
        // Single quadrants:
        static ref quad1 :Interval = Interval::new(0., PI/2.);
        static ref quad2 :Interval = Interval::new(PI/2., -PI); // equivalent to (pi/2., pi)
        static ref quad3 :Interval = Interval::new(PI, -PI/2.);
        static ref quad4 :Interval = Interval::new(-PI/2., 0.);
        // Quadrant pairs:
        static ref quad12 :Interval = Interval::new(0., -PI);
        static ref quad23 :Interval = Interval::new(PI/2., -PI/2.);
        static ref quad34 :Interval = Interval::new(-PI, 0.);
        static ref quad41 :Interval = Interval::new(-PI/2., PI/2.);
        // Quadrant triples:
        static ref quad123 :Interval = Interval::new(0., -PI/2.);
        static ref quad234 :Interval = Interval::new(PI/2., 0.);
        static ref quad341 :Interval = Interval::new(PI, PI/2.);
        static ref quad412 :Interval = Interval::new(-PI/2., -PI);
        // Small intervals around the midpoints between quadrants,
        // such that the center of each interval is offset slightly CCW from the midpoint.
        static ref mid12 :Interval = Interval::new(PI/2.-0.01, PI/2.+0.02);
        static ref mid23 :Interval = Interval::new(PI-0.01, -PI+0.02);
        static ref mid34 :Interval = Interval::new(-PI/2.-0.01, -PI/2.+0.02);
        static ref mid41 :Interval = Interval::new(-0.01, 0.02);
    }

    #[test]
    fn test_interval_constructors() {
        // Check that [-π,-π] is normalized to [π,π].
        assert_eq!(mipi.lo, PI);
        assert_eq!(mipi.hi, PI);

        let i = Interval::default();
        assert!(i.is_valid(), "default interval is not valid");
    }

    #[test]
    fn test_interval_from_point_pair() {
        assert_eq!(*pi, Interval::from_point_pair(-PI, PI));
        assert_eq!(*pi, Interval::from_point_pair(PI, -PI));
        assert_eq!(*mid34, Interval::from_point_pair(mid34.hi, mid34.lo));
        assert_eq!(*mid23, Interval::from_point_pair(mid23.lo, mid23.hi));
    }

    #[test]
    fn test_interval_simple_predicates() {
        assert!(zero.is_valid() && !zero.is_empty() && !zero.is_full());
        assert!(empty.is_valid() && empty.is_empty() && !empty.is_full());
        assert!(empty.is_inverted());

        assert!(full.is_valid() && !full.is_empty() && full.is_full());
        assert!(pi.is_valid() && !pi.is_empty() && !pi.is_inverted());
        assert!(mipi.is_valid() && !mipi.is_empty() && !mipi.is_inverted());
    }

    #[test]
    fn test_interval_almost_full_or_empty() {
        // Test that rounding errors don't cause intervals that are almost empty or
        // full to be considered empty or full.  The following value is the greatest
        // representable value less than Pi.
        let almost_pi = PI - 2. * DBL_EPSILON;

        assert!(!Interval::new(-almost_pi, almost_pi).is_full());
        assert!(!Interval::new(-PI, almost_pi).is_full());
        assert!(!Interval::new(PI, -almost_pi).is_full());
        assert!(!Interval::new(almost_pi, -PI).is_full());
    }

    fn test_center_case(expected: f64, i: Interval) {
        assert_f64_eq!(expected, i.center());
    }

    #[test]
    fn test_interval_center() {
        test_center_case(PI / 2., *quad12);
        test_center_case(3. - PI, Interval::new(3.1, 2.9));
        test_center_case(PI - 3., Interval::new(-2.9, -3.1));
        test_center_case(PI, Interval::new(2.1, -2.1));

        test_center_case(PI, *pi);
        test_center_case(PI, *mipi);
        test_center_case(PI, *quad23);
        test_center_case(0.75 * PI, *quad123);
    }

    #[test]
    fn test_interval_len() {
        assert!(empty.len() < 0.);

        assert_f64_eq!(PI, quad12.len());
        assert_f64_eq!(0., pi.len());
        assert_f64_eq!(0., mipi.len());
        assert_f64_eq!(1.5 * PI, quad123.len());
        assert_f64_eq!(PI, quad23.len());
        assert_f64_eq!(2. * PI, full.len());
    }

    fn test_contains_case(
        i: Interval,
        p_in: &[f64],
        p_out: &[f64],
        p_i_in: &[f64],
        p_i_out: &[f64],
    ) {
        for &p in p_in {
            assert!(i.contains(p));
        }
        for &p in p_out {
            assert!(!i.contains(p));
        }

        for &p in p_i_in {
            assert!(i.interior_contains(p));
        }
        for &p in p_i_out {
            assert!(!i.interior_contains(p));
        }
    }

    #[test]
    fn test_interval_contains() {
        test_contains_case(*empty, &[], &[0., PI, -PI], &[], &[PI, -PI]);
        test_contains_case(*full, &[0., PI, -PI], &[], &[PI, -PI], &[]);
        test_contains_case(*quad12, &[0., PI, -PI], &[], &[PI / 2.], &[0., PI, -PI]);
        test_contains_case(
            *quad23,
            &[PI / 2., -PI / 2., PI, -PI],
            &[0.],
            &[PI, -PI],
            &[PI / 2., -PI / 2., 0.],
        );
        test_contains_case(*pi, &[PI, -PI], &[0.], &[], &[PI, -PI]);
        test_contains_case(*mipi, &[PI, -PI], &[0.], &[], &[PI, -PI]);
        test_contains_case(*zero, &[0.], &[], &[], &[0.]);
    }

    fn iops_case(
        x: &Interval,
        y: &Interval,
        x_contains_y: bool,
        x_interior_contains_y: bool,
        x_intersects_y: bool,
        x_interior_intersects_y: bool,
        want_union: &Interval,
        want_intersection: &Interval,
    ) {
        assert_eq!(x_contains_y, x.contains_interval(&y));
        assert_eq!(x_interior_contains_y, x.interior_contains_interval(&y));

        assert_eq!(x_intersects_y, x.intersects(&y));
        assert_eq!(x_interior_intersects_y, x.interior_intersects(&y));

        assert_eq!(*want_intersection, x.intersection(&y));
        assert_eq!(*want_union, x.union(&y));
    }

    #[test]
    fn test_interval_operations() {
        let quad12eps = Interval::new(quad12.lo, mid23.hi);
        let quad2hi = Interval::new(mid23.lo, quad12.hi);
        let quad412eps = Interval::new(mid34.lo, quad12.hi);
        let quadeps12 = Interval::new(mid41.lo, quad12.hi);
        let quad1lo = Interval::new(quad12.lo, mid41.hi);
        let quad2lo = Interval::new(quad23.lo, mid12.hi);
        let quad3hi = Interval::new(mid34.lo, quad23.hi);
        let quadeps23 = Interval::new(mid12.lo, quad23.hi);
        let quad23eps = Interval::new(quad23.lo, mid34.hi);
        let quadeps123 = Interval::new(mid41.lo, quad23.hi);

        iops_case(&empty, &empty, true, true, false, false, &empty, &empty);
        iops_case(&empty, &full, false, false, false, false, &full, &empty);
        iops_case(&empty, &zero, false, false, false, false, &zero, &empty);
        iops_case(&empty, &pi, false, false, false, false, &pi, &empty);
        iops_case(&empty, &mipi, false, false, false, false, &mipi, &empty);

        // 5
        iops_case(&full, &empty, true, true, false, false, &full, &empty);
        iops_case(&full, &full, true, true, true, true, &full, &full);
        iops_case(&full, &zero, true, true, true, true, &full, &zero);
        iops_case(&full, &pi, true, true, true, true, &full, &pi);
        iops_case(&full, &mipi, true, true, true, true, &full, &mipi);
        iops_case(&full, &quad12, true, true, true, true, &full, &quad12);
        iops_case(&full, &quad23, true, true, true, true, &full, &quad23);

        // 12
        iops_case(&zero, &empty, true, true, false, false, &zero, &empty);
        iops_case(&zero, &full, false, false, true, false, &full, &zero);
        iops_case(&zero, &zero, true, false, true, false, &zero, &zero);
        iops_case(
            &zero,
            &pi,
            false,
            false,
            false,
            false,
            &Interval::new(0., PI),
            &empty,
        );
        iops_case(&zero, &pi2, false, false, false, false, &quad1, &empty);
        iops_case(&zero, &mipi, false, false, false, false, &quad12, &empty);
        iops_case(&zero, &mipi2, false, false, false, false, &quad4, &empty);
        iops_case(&zero, &quad12, false, false, true, false, &quad12, &zero);
        iops_case(&zero, &quad23, false, false, false, false, &quad123, &empty);

        // 21
        iops_case(&pi2, &empty, true, true, false, false, &pi2, &empty);
        iops_case(&pi2, &full, false, false, true, false, &full, &pi2);
        iops_case(&pi2, &zero, false, false, false, false, &quad1, &empty);
        iops_case(
            &pi2,
            &pi,
            false,
            false,
            false,
            false,
            &Interval::new(PI / 2., PI),
            &empty,
        );
        iops_case(&pi2, &pi2, true, false, true, false, &pi2, &pi2);
        iops_case(&pi2, &mipi, false, false, false, false, &quad2, &empty);
        iops_case(&pi2, &mipi2, false, false, false, false, &quad23, &empty);
        iops_case(&pi2, &quad12, false, false, true, false, &quad12, &pi2);
        iops_case(&pi2, &quad23, false, false, true, false, &quad23, &pi2);

        // 30
        iops_case(&pi, &empty, true, true, false, false, &pi, &empty);
        iops_case(&pi, &full, false, false, true, false, &full, &pi);
        iops_case(
            &pi,
            &zero,
            false,
            false,
            false,
            false,
            &Interval::new(PI, 0.),
            &empty,
        );
        iops_case(&pi, &pi, true, false, true, false, &pi, &pi);
        iops_case(
            &pi,
            &pi2,
            false,
            false,
            false,
            false,
            &Interval::new(PI / 2., PI),
            &empty,
        );
        iops_case(&pi, &mipi, true, false, true, false, &pi, &pi);
        iops_case(&pi, &mipi2, false, false, false, false, &quad3, &empty);
        iops_case(
            &pi,
            &quad12,
            false,
            false,
            true,
            false,
            &Interval::new(0., PI),
            &pi,
        );
        iops_case(&pi, &quad23, false, false, true, false, &quad23, &pi);

        // 39
        iops_case(&mipi, &empty, true, true, false, false, &mipi, &empty);
        iops_case(&mipi, &full, false, false, true, false, &full, &mipi);
        iops_case(&mipi, &zero, false, false, false, false, &quad34, &empty);
        iops_case(&mipi, &pi, true, false, true, false, &mipi, &mipi);
        iops_case(&mipi, &pi2, false, false, false, false, &quad2, &empty);
        iops_case(&mipi, &mipi, true, false, true, false, &mipi, &mipi);
        iops_case(
            &mipi,
            &mipi2,
            false,
            false,
            false,
            false,
            &Interval::new(-PI, -PI / 2.),
            &empty,
        );
        iops_case(&mipi, &quad12, false, false, true, false, &quad12, &mipi);
        iops_case(&mipi, &quad23, false, false, true, false, &quad23, &mipi);

        // 48
        iops_case(&quad12, &empty, true, true, false, false, &quad12, &empty);
        iops_case(&quad12, &full, false, false, true, true, &full, &quad12);
        iops_case(&quad12, &zero, true, false, true, false, &quad12, &zero);
        iops_case(&quad12, &pi, true, false, true, false, &quad12, &pi);
        iops_case(&quad12, &mipi, true, false, true, false, &quad12, &mipi);
        iops_case(&quad12, &quad12, true, false, true, true, &quad12, &quad12);
        iops_case(&quad12, &quad23, false, false, true, true, &quad123, &quad2);
        iops_case(&quad12, &quad34, false, false, true, false, &full, &quad12);

        // 56
        iops_case(&quad23, &empty, true, true, false, false, &quad23, &empty);
        iops_case(&quad23, &full, false, false, true, true, &full, &quad23);
        iops_case(&quad23, &zero, false, false, false, false, &quad234, &empty);
        iops_case(&quad23, &pi, true, true, true, true, &quad23, &pi);
        iops_case(&quad23, &mipi, true, true, true, true, &quad23, &mipi);
        iops_case(&quad23, &quad12, false, false, true, true, &quad123, &quad2);
        iops_case(&quad23, &quad23, true, false, true, true, &quad23, &quad23);
        iops_case(
            &quad23,
            &quad34,
            false,
            false,
            true,
            true,
            &quad234,
            &Interval::new(-PI, -PI / 2.),
        );

        // 64
        iops_case(
            &quad1,
            &quad23,
            false,
            false,
            true,
            false,
            &quad123,
            &Interval::new(PI / 2., PI / 2.),
        );
        iops_case(&quad2, &quad3, false, false, true, false, &quad23, &mipi);
        iops_case(&quad3, &quad2, false, false, true, false, &quad23, &pi);
        iops_case(&quad2, &pi, true, false, true, false, &quad2, &pi);
        iops_case(&quad2, &mipi, true, false, true, false, &quad2, &mipi);
        iops_case(&quad3, &pi, true, false, true, false, &quad3, &pi);
        iops_case(&quad3, &mipi, true, false, true, false, &quad3, &mipi);

        // 71
        iops_case(&quad12, &mid12, true, true, true, true, &quad12, &mid12);
        iops_case(&mid12, &quad12, false, false, true, true, &quad12, &mid12);

        // 73
        iops_case(
            &quad12, &mid23, false, false, true, true, &quad12eps, &quad2hi,
        );
        iops_case(
            &mid23, &quad12, false, false, true, true, &quad12eps, &quad2hi,
        );

        // This test checks that the union of two disjoint intervals is the smallest
        // interval that contains both of them.  Note that the center of "mid34"
        // slightly CCW of -Pi/2 so that there is no ambiguity about the result.
        // 75
        iops_case(
            &quad12,
            &mid34,
            false,
            false,
            false,
            false,
            &quad412eps,
            &empty,
        );
        iops_case(
            &mid34,
            &quad12,
            false,
            false,
            false,
            false,
            &quad412eps,
            &empty,
        );

        // 77
        iops_case(
            &quad12, &mid41, false, false, true, true, &quadeps12, &quad1lo,
        );
        iops_case(
            &mid41, &quad12, false, false, true, true, &quadeps12, &quad1lo,
        );

        // 79
        iops_case(
            &quad23, &mid12, false, false, true, true, &quadeps23, &quad2lo,
        );
        iops_case(
            &mid12, &quad23, false, false, true, true, &quadeps23, &quad2lo,
        );
        iops_case(&quad23, &mid23, true, true, true, true, &quad23, &mid23);
        iops_case(&mid23, &quad23, false, false, true, true, &quad23, &mid23);
        iops_case(
            &quad23, &mid34, false, false, true, true, &quad23eps, &quad3hi,
        );
        iops_case(
            &mid34, &quad23, false, false, true, true, &quad23eps, &quad3hi,
        );
        iops_case(
            &quad23,
            &mid41,
            false,
            false,
            false,
            false,
            &quadeps123,
            &empty,
        );
        iops_case(
            &mid41,
            &quad23,
            false,
            false,
            false,
            false,
            &quadeps123,
            &empty,
        );
    }

    fn test_interval_add_point_case(want: Interval, mut i: Interval, points: &[f64]) {
        for &p in points {
            i = i + p;
        }
        assert_eq!(want, i);
    }

    #[test]
    fn test_interval_add_point() {
        test_interval_add_point_case(*zero, *empty, &[0.]);
        test_interval_add_point_case(*pi, *empty, &[PI]);
        test_interval_add_point_case(*mipi, *empty, &[-PI]);
        test_interval_add_point_case(*pi, *empty, &[PI, -PI]);
        test_interval_add_point_case(*mipi, *empty, &[-PI, PI]);
        test_interval_add_point_case(*mid12, *empty, &[mid12.lo, mid12.hi]);
        test_interval_add_point_case(*mid23, *empty, &[mid23.lo, mid23.hi]);

        test_interval_add_point_case(*quad123, *quad1, &[-0.9 * PI, -PI / 2.]);
        test_interval_add_point_case(*full, *full, &[0.]);
        test_interval_add_point_case(*full, *full, &[PI]);
        test_interval_add_point_case(*full, *full, &[-PI]);
    }

    #[test]
    fn test_interval_expanded() {
        assert_eq!(*empty, empty.expanded(1.));
        assert_eq!(*full, full.expanded(1.));
        assert_eq!(Interval::new(-1., 1.), zero.expanded(1.));
        assert_eq!(Interval::new(PI - 0.01, -PI + 0.01), mipi.expanded(0.01));
        assert_eq!(*full, pi.expanded(27.));
        assert_eq!(*quad23, pi.expanded(PI / 2.));
        assert_eq!(*quad12, pi2.expanded(PI / 2.));
        assert_eq!(*quad34, mipi2.expanded(PI / 2.));

        assert_eq!(*empty, empty.expanded(-1.));
        assert_eq!(*full, full.expanded(-1.));
        assert_eq!(*empty, quad123.expanded(-27.));
        assert_eq!(*empty, quad234.expanded(-27.));
        assert_eq!(*quad2, quad123.expanded(-PI / 2.));
        assert_eq!(*quad4, quad341.expanded(-PI / 2.));
        assert_eq!(*quad1, quad412.expanded(-PI / 2.));
    }
}
