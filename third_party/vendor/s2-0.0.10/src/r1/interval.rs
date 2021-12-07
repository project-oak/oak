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

use crate::consts::EPSILON;

/// Interval represents a closed interval on ℝ.
/// Zero-length intervals (where Lo == Hi) represent single points.
/// If Lo > Hi then the interval is empty.
#[derive(Clone, Copy, Default)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Interval {
    /// lower bound of the interval
    pub lo: f64,
    /// upper bound of the interval
    pub hi: f64,
}
impl std::fmt::Debug for Interval {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "[{:.7}, {:.7}]", self.lo, self.hi)
    }
}

/// An empty interval.
pub const EMPTY: Interval = Interval { lo: 1., hi: 0. };

impl Interval {
    pub fn new(lo: f64, hi: f64) -> Self {
        Self { lo, hi }
    }

    /// from_point returns an interval representing a single point.
    pub fn from_point(p: f64) -> Self {
        Self { lo: p, hi: p }
    }

    /// is_empty reports whether the interval is empty.
    pub fn is_empty(&self) -> bool {
        self.lo > self.hi
    }

    /// center returns the midpoint of the interval.
    /// It is undefined for empty intervals.
    pub fn center(&self) -> f64 {
        0.5 * (self.lo + self.hi)
    }

    /// len returns the length of the interval.
    /// The length of an empty interval is negative.
    pub fn len(&self) -> f64 {
        self.hi - self.lo
    }

    /// contains returns true iff the interval contains p.
    pub fn contains(&self, p: f64) -> bool {
        self.lo <= p && p <= self.hi
    }

    /// contains_interval returns true iff the interval contains oi.
    pub fn contains_interval(&self, oi: &Self) -> bool {
        if oi.is_empty() {
            true
        } else {
            self.lo <= oi.lo && oi.hi <= self.hi
        }
    }

    /// interior_contains returns true iff the the interval strictly contains p.
    pub fn interior_contains(&self, p: f64) -> bool {
        self.lo < p && p < self.hi
    }

    /// interior_contains_interval returns true iff the interval strictly contains oi.
    pub fn interior_contains_interval(&self, oi: &Self) -> bool {
        if oi.is_empty() {
            true
        } else {
            self.lo < oi.lo && oi.hi < self.hi
        }
    }

    /// intersects returns true iff the interval contains any points in common with oi.
    pub fn intersects(&self, oi: &Self) -> bool {
        if self.lo <= oi.lo {
            // oi.Lo ∈ i and oi is not empty
            oi.lo <= self.hi && oi.lo <= oi.hi
        } else {
            // i.Lo ∈ oi and i is not empty
            self.lo <= oi.hi && self.lo <= self.hi
        }
    }

    /// interior_intersects returns true iff the interior of the interval contains any points in
    /// common with oi, including the latter's boundary.
    pub fn interior_intersects(&self, oi: &Self) -> bool {
        oi.lo < self.hi && self.lo < oi.hi && self.lo < self.hi && oi.lo <= oi.hi
    }

    /// intersection returns the interval containing all points common to i and j.
    pub fn intersection(&self, other: &Self) -> Self {
        // Empty intervals do not need to be special-cased.
        Interval {
            lo: self.lo.max(other.lo),
            hi: self.hi.min(other.hi),
        }
    }

    /// clamp_point returns the closest point in the interval to the given point "p".
    /// The interval must be non-empty.
    pub fn clamp_point(&self, p: f64) -> f64 {
        self.lo.max(self.hi.min(p))
    }

    /// expanded returns an interval that has been expanded on each side by margin.
    /// If margin is negative, then the function shrinks the interval on
    /// each side by margin instead. The resulting interval may be empty. Any
    /// expansion of an empty interval remains empty.
    pub fn expanded(&self, margin: f64) -> Self {
        if self.is_empty() {
            *self
        } else {
            Interval {
                lo: self.lo - margin,
                hi: self.hi + margin,
            }
        }
    }

    /// union returns the smallest interval that contains this interval and the given interval.
    pub fn union(&self, other: &Self) -> Self {
        if self.is_empty() {
            *other
        } else if other.is_empty() {
            *self
        } else {
            Interval {
                lo: self.lo.min(other.lo),
                hi: self.hi.max(other.hi),
            }
        }
    }

    /// approx_eq reports whether the interval can be transformed into the
    /// given interval by moving each endpoint a small distance.
    /// The empty interval is considered to be positioned arbitrarily on the
    /// real line, so any interval with a small enough length will match
    /// the empty interval.
    pub fn approx_eq(&self, other: &Self) -> bool {
        if self.is_empty() {
            other.len() < 2. * EPSILON
        } else if other.is_empty() {
            self.len() < 2. * EPSILON
        } else {
            (self.lo - other.lo).abs() <= EPSILON && (self.hi - other.hi).abs() <= EPSILON
        }
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
    /// returns the interval expanded so that it contains the given point.
    fn add(self, p: f64) -> Self::Output {
        if self.is_empty() {
            Interval { lo: p, hi: p }
        } else if p < self.lo {
            Interval { lo: p, hi: self.hi }
        } else if p > self.hi {
            Interval { lo: self.lo, hi: p }
        } else {
            *self
        }
    }
}

impl std::cmp::PartialEq<Interval> for Interval {
    /// returns true iff the interval contains the same points as other.
    fn eq(&self, other: &Interval) -> bool {
        (self.lo == other.lo && self.hi == other.hi) || (self.is_empty() && other.is_empty())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! I {
        ($lo:expr, $hi:expr) => {
            Interval { lo: $lo, hi: $hi }
        };
    }

    const UNIT: Interval = I! {0., 1.};
    const NEG_UNIT: Interval = I! {-1., 0.};
    const HALF: Interval = I! {0.5, 0.5};
    const ZERO: Interval = I! {0., 0.};

    #[test]
    fn is_empty() {
        assert_eq!(false, UNIT.is_empty());
        assert_eq!(false, HALF.is_empty());
        assert_eq!(true, EMPTY.is_empty());
        assert_eq!(false, ZERO.is_empty());
    }

    #[test]
    fn center() {
        assert_eq!(UNIT.center(), 0.5);
        assert_eq!(NEG_UNIT.center(), -0.5);
        assert_eq!(HALF.center(), 0.5);
    }

    #[test]
    fn length() {
        assert_eq!(UNIT.len(), 1.);
        assert_eq!(NEG_UNIT.len(), 1.);
        assert_eq!(HALF.len(), 0.);
    }

    #[test]
    fn interval_contains() {
        assert_eq!(true, UNIT.contains(0.5));
        assert_eq!(true, UNIT.interior_contains(0.5));

        assert_eq!(true, UNIT.contains(0.));
        assert_eq!(false, UNIT.interior_contains(0.));

        assert_eq!(true, UNIT.contains(1.));
        assert_eq!(false, UNIT.interior_contains(1.));
    }

    fn test_interval_ops(
        have: &Interval,
        other: &Interval,
        contains: bool,
        interior_contains: bool,
        intersects: bool,
        interior_intersects: bool,
    ) {
        assert_eq!(contains, have.contains_interval(other));
        assert_eq!(interior_contains, have.interior_contains_interval(other));
        assert_eq!(intersects, have.intersects(other));
        assert_eq!(interior_intersects, have.interior_intersects(other));
    }

    #[test]
    fn interval_operations() {
        test_interval_ops(&EMPTY, &EMPTY, true, true, false, false);
        test_interval_ops(&EMPTY, &UNIT, false, false, false, false);
        test_interval_ops(&UNIT, &HALF, true, true, true, true);
        test_interval_ops(&UNIT, &UNIT, true, false, true, true);
        test_interval_ops(&UNIT, &EMPTY, true, true, false, false);
        test_interval_ops(&UNIT, &NEG_UNIT, false, false, true, false);
    }

    #[test]
    fn intersection() {
        assert_eq!(HALF, UNIT.intersection(&HALF));
        assert_eq!(ZERO, UNIT.intersection(&NEG_UNIT));
        assert_eq!(EMPTY, NEG_UNIT.intersection(&HALF));
        assert_eq!(EMPTY, UNIT.intersection(&EMPTY));
        assert_eq!(EMPTY, EMPTY.intersection(&UNIT));
    }

    fn test_union(x: Interval, y: Interval, want: Interval) {
        assert_eq!(want, x.union(&y));
        assert_eq!(want, y.union(&x));
    }

    #[test]
    fn union() {
        let i_99_100 = Interval { lo: 99., hi: 100. };
        test_union(i_99_100.clone(), EMPTY, i_99_100.clone());
        test_union(I!(5., 3.), I!(0., -2.), EMPTY);
        test_union(UNIT, UNIT, UNIT);
        test_union(UNIT, NEG_UNIT, I!(-1., 1.));
        test_union(HALF, UNIT, UNIT);
    }

    #[test]
    fn add() {
        assert_eq!(I!(5., 5.), EMPTY + 5.);
        assert_eq!(I!(-1., 5.), I!(5., 5.) + -1.);
        assert_eq!(I!(-1., 5.), I!(-1., 5.) + -1.);
        assert_eq!(I!(-1., 6.), I!(-1., 5.) + 6.);
    }

    #[test]
    fn clamp_point() {
        let i = I!(0.1, 0.4);
        assert_eq!(0.3, i.clamp_point(0.3));
        assert_eq!(0.1, i.clamp_point(-7.0));
        assert_eq!(0.4, i.clamp_point(0.6));
    }

    #[test]
    fn expanded() {
        assert_eq!(EMPTY, EMPTY.expanded(0.45));
        assert_eq!(I!(-0.5, 1.5), UNIT.expanded(0.5));
        assert_eq!(I!(0.5, 0.5), UNIT.expanded(-0.5));
        assert_eq!(EMPTY, UNIT.expanded(-0.51));
    }

    fn test_approx_eq(i1: &Interval, i2: &Interval, expected: bool) {
        assert_eq!(expected, i1.approx_eq(&i2));
    }

    #[test]
    fn approx_equal() {
        test_approx_eq(&EMPTY, &EMPTY, true);
        test_approx_eq(&EMPTY, &ZERO, true);
        test_approx_eq(&EMPTY, &I!(1., 1.), true);
        test_approx_eq(&EMPTY, &I!(0., 1.), false);
        test_approx_eq(&EMPTY, &I!(1., 1. + 2. * EPSILON), true);

        test_approx_eq(&I!(1., 1.), &I!(1., 1.), true);
        test_approx_eq(&I!(1., 1.), &I!(1. - EPSILON, 1. - EPSILON), true);
        test_approx_eq(&I!(1., 1.), &I!(1. + EPSILON, 1. + EPSILON), true);
        test_approx_eq(&I!(1., 1.), &I!(1. - 3. * EPSILON, 1.), false);
        test_approx_eq(&I!(1., 1.), &I!(1. - EPSILON, 1. + EPSILON), true);
        test_approx_eq(&ZERO, &I!(1., 1.), false);

        test_approx_eq(&I!(1. - EPSILON, 2. + EPSILON), &I!(1., 2.), false);
        test_approx_eq(&I!(1. + EPSILON, 2. - EPSILON), &I!(1., 2.), true);
        test_approx_eq(&I!(1. - 3. * EPSILON, 2. + EPSILON), &I!(1., 2.), false);
        test_approx_eq(&I!(1. + 3. * EPSILON, 2. - EPSILON), &I!(1., 2.), false);
        test_approx_eq(&I!(1. - EPSILON, 2. + 3. * EPSILON), &I!(1., 2.), false);
        test_approx_eq(&I!(1. + EPSILON, 2. - 3. * EPSILON), &I!(1., 2.), false);
    }
}
