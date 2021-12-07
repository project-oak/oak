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

use std;
use std::f64::consts::PI;

use crate::consts::*;
use crate::s1::angle::*;

/// ChordAngle represents the angle subtended by a chord (i.e., the straight
/// line segment connecting two points on the sphere). Its representation
/// makes it very efficient for computing and comparing distances, but unlike
/// Angle it is only capable of representing angles between 0 and π radians.
/// Generally, ChordAngle should only be used in loops where many angles need
/// to be calculated and compared. Otherwise it is simpler to use Angle.
///
/// ChordAngle loses some accuracy as the angle approaches π radians.
/// Specifically, the representation of (π - x) radians has an error of about
/// (1e-15 / x), with a maximum error of about 2e-8 radians (about 13cm on the
/// Earth's surface). For comparison, for angles up to π/2 radians (10000km)
/// the worst-case representation error is about 2e-16 radians (1 nanonmeter),
/// which is about the same as Angle.
///
/// ChordAngles are represented by the squared chord length, which can
/// range from 0 to 4. Positive infinity represents an infinite squared length.
#[derive(Clone, Copy, PartialEq, PartialOrd, Debug, Default)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ChordAngle(pub f64);

/// NEGATIVE represents a chord angle smaller than the zero angle.
/// The only valid operations on a NegativeChordAngle are comparisons and
/// Angle conversions.
pub const NEGATIVE: ChordAngle = ChordAngle(-1f64);

/// RIGHT represents a chord angle of 90 degrees (a "right angle").
pub const RIGHT: ChordAngle = ChordAngle(2f64);

/// STRAIGHT represents a chord angle of 180 degrees (a "straight angle").
/// This is the maximum finite chord angle.
pub const STRAIGHT: ChordAngle = ChordAngle(4f64);

impl<'a> From<&'a Angle> for ChordAngle {
    /// returns a ChordAngle from the given Angle.
    fn from(a: &'a Angle) -> Self {
        if a.rad() < 0. {
            NEGATIVE
        } else if a.is_infinite() {
            ChordAngle::inf()
        } else {
            let l = 2. * (0.5 * a.rad().min(PI)).sin();
            ChordAngle(l * l)
        }
    }
}
impl From<Angle> for ChordAngle {
    /// returns a ChordAngle from the given Angle.
    fn from(a: Angle) -> Self {
        ChordAngle::from(&a)
    }
}

impl<'a> From<&'a Deg> for ChordAngle {
    fn from(a: &'a Deg) -> Self {
        Angle::from(a).into()
    }
}
impl From<Deg> for ChordAngle {
    fn from(a: Deg) -> Self {
        Angle::from(&a).into()
    }
}

impl<'a> From<&'a ChordAngle> for Angle {
    /// converts this ChordAngle to an Angle.
    fn from(ca: &'a ChordAngle) -> Self {
        if ca.0 < 0. {
            Rad(-1.).into()
        } else if ca.is_infinite() {
            Angle::inf()
        } else {
            Rad(2. * (0.5 * ca.0.sqrt()).asin()).into()
        }
    }
}
impl From<ChordAngle> for Angle {
    /// converts this ChordAngle to an Angle.
    fn from(ca: ChordAngle) -> Self {
        Angle::from(&ca)
    }
}

impl<'a, 'b> std::ops::Add<&'a ChordAngle> for &'b ChordAngle {
    type Output = ChordAngle;
    /// add adds the other ChordAngle to this one and returns the resulting value.
    /// This method assumes the ChordAngles are not special.
    fn add(self, other: &'a ChordAngle) -> Self::Output {
        // Note that this method (and Sub) is much more efficient than converting
        // the ChordAngle to an Angle and adding those and converting back. It
        // requires only one square root plus a few additions and multiplications.

        if other.0 == 0.0 {
            // Optimization for the common case where b is an error tolerance
            // parameter that happens to be set to zero.
            *self
        } else if self.0 + other.0 >= 4. {
            // Clamp the angle sum to at most 180 degrees.
            STRAIGHT
        } else {
            // Let a and b be the (non-squared) chord lengths, and let c = a+b.
            // Let A, B, and C be the corresponding half-angles (a = 2*sin(A), etc).
            // Then the formula below can be derived from c = 2 * sin(A+B) and the
            // relationships   sin(A+B) = sin(A)*cos(B) + sin(B)*cos(A)
            //                 cos(X) = sqrt(1 - sin^2(X))
            let x = self.0 * (1. - 0.25 * other.0);
            let y = other.0 * (1. - 0.25 * self.0);
            ChordAngle(4f64.min(x + y + 2f64 * (x * y).sqrt()))
        }
    }
}

impl std::ops::Add<ChordAngle> for ChordAngle {
    type Output = ChordAngle;
    fn add(self, other: ChordAngle) -> Self::Output {
        &self + &other
    }
}

impl std::ops::Sub<ChordAngle> for ChordAngle {
    type Output = ChordAngle;
    /// sub subtracts the other ChordAngle from this one and returns the resulting
    /// value. This method assumes the ChordAngles are not special.
    fn sub(self, other: ChordAngle) -> Self::Output {
        if other.0 == 0.0 {
            self
        } else if self.0 <= other.0 {
            ChordAngle(0f64)
        } else {
            let x = self.0 * (1. - 0.25 * other.0);
            let y = other.0 * (1. - 0.25 * self.0);
            ChordAngle(0f64.max(x + y - 2. * (x * y).sqrt()))
        }
    }
}

impl ChordAngle {
    /// inf returns a chord angle larger than any finite chord angle.
    /// The only valid operations on an InfChordAngle are comparisons and Angle conversions.
    pub fn inf() -> Self {
        ChordAngle(std::f64::INFINITY)
    }

    /// is_infinite reports whether this ChordAngle is infinite.
    pub fn is_infinite(&self) -> bool {
        self.0.is_infinite()
    }

    /// from_squared_length returns a ChordAngle from the squared chord length.
    /// Note that the argument is automatically clamped to a maximum of 4.0 to
    /// handle possible roundoff errors. The argument must be non-negative.
    pub fn from_squared_length(length2: f64) -> Self {
        if length2 > 4. {
            STRAIGHT
        } else {
            ChordAngle(length2)
        }
    }

    /// expanded returns a new ChordAngle that has been adjusted by the given error
    /// bound (which can be positive or negative). Error should be the value
    /// returned by either MaxPointError or MaxAngleError. For example:
    ///     let a = ChordAngle::from_points(x, y)
    ///     let a1 = a.expanded(a.max_point_error())
    pub fn expanded(&self, e: f64) -> Self {
        // If the angle is special, don't change it. Otherwise clamp it to the valid range.
        if self.is_special() {
            *self
        } else {
            ChordAngle(0f64.max(4f64.min(self.0 + e)))
        }
    }

    /// is_special reports whether this ChordAngle is one of the special cases.
    pub fn is_special(&self) -> bool {
        self.0 < 0. || self.0.is_infinite()
    }

    /// is_valid reports whether this ChordAngle is valid or not.
    pub fn is_valid(&self) -> bool {
        self.0 >= 0. && self.0 <= 4. || self.is_special()
    }

    /// max_point_error returns the maximum error size for a ChordAngle constructed
    /// from 2 Points x and y, assuming that x and y are normalized to within the
    /// bounds guaranteed by s2.Point.Normalize. The error is defined with respect to
    /// the true distance after the points are projected to lie exactly on the sphere.
    pub fn max_point_error(&self) -> f64 {
        // There is a relative error of (2.5*DBL_EPSILON) when computing the squared
        // distance, plus an absolute error of (16 * DBL_EPSILON**2) because the
        // lengths of the input points may differ from 1 by up to (2*DBL_EPSILON) each.
        2.5 * DBL_EPSILON * self.0 + 16. * DBL_EPSILON * DBL_EPSILON
    }

    /// max_angle_error returns the maximum error for a ChordAngle constructed
    /// as an Angle distance.
    pub fn max_angle_error(&self) -> f64 {
        DBL_EPSILON * self.0
    }

    /// sin returns the sine of this chord angle. This method is more efficient
    /// than converting to Angle and performing the computation.
    pub fn sin(&self) -> f64 {
        self.sin2().sqrt()
    }

    /// sin2 returns the square of the sine of this chord angle.
    /// It is more efficient than Sin.
    pub fn sin2(&self) -> f64 {
        // Let a be the (non-squared) chord length, and let A be the corresponding
        // half-angle (a = 2*sin(A)).  The formula below can be derived from:
        //   sin(2*A) = 2 * sin(A) * cos(A)
        //   cos^2(A) = 1 - sin^2(A)
        // This is much faster than converting to an angle and computing its sine.
        self.0 * (1. - 0.25 * self.0)
    }

    /// cos returns the cosine of this chord angle. This method is more efficient
    /// than converting to Angle and performing the computation.
    pub fn cos(&self) -> f64 {
        // cos(2*A) = cos^2(A) - sin^2(A) = 1 - 2*sin^2(A)
        1.0 - 0.5 * self.0
    }

    /// tan returns the tangent of this chord angle.
    pub fn tan(&self) -> f64 {
        self.sin() / self.cos()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_chordangle_basics_case(ca1: ChordAngle, ca2: ChordAngle, less_than: bool, equal: bool) {
        assert_eq!(less_than, ca1 < ca2);
        assert_eq!(equal, ca1 == ca2);
    }

    #[test]
    fn test_chordangle_basics() {
        let zero = ChordAngle::default();

        test_chordangle_basics_case(NEGATIVE, NEGATIVE, false, true);
        test_chordangle_basics_case(NEGATIVE, zero, true, false);
        test_chordangle_basics_case(NEGATIVE, STRAIGHT, true, false);
        test_chordangle_basics_case(NEGATIVE, ChordAngle::inf(), true, false);

        test_chordangle_basics_case(zero, zero, false, true);
        test_chordangle_basics_case(zero, STRAIGHT, true, false);
        test_chordangle_basics_case(zero, ChordAngle::inf(), true, false);

        test_chordangle_basics_case(STRAIGHT, STRAIGHT, false, true);
        test_chordangle_basics_case(STRAIGHT, ChordAngle::inf(), true, false);

        test_chordangle_basics_case(ChordAngle::inf(), ChordAngle::inf(), false, true);
        test_chordangle_basics_case(ChordAngle::inf(), ChordAngle::inf(), false, true);
    }

    fn test_chordangle_is_functions_case(
        ca: ChordAngle,
        is_neg: bool,
        is_zero: bool,
        is_inf: bool,
        is_special: bool,
    ) {
        assert_eq!(is_neg, ca.0 < 0.);
        assert_eq!(is_zero, ca.0 == 0.);
        assert_eq!(is_inf, ca.is_infinite());
        assert_eq!(is_special, ca.is_special());
    }

    #[test]
    fn test_chordangle_is_functions() {
        let zero: ChordAngle = Default::default();
        test_chordangle_is_functions_case(zero, false, true, false, false);
        test_chordangle_is_functions_case(NEGATIVE, true, false, false, true);
        test_chordangle_is_functions_case(zero, false, true, false, false);
        test_chordangle_is_functions_case(STRAIGHT, false, false, false, false);
        test_chordangle_is_functions_case(ChordAngle::inf(), false, false, true, true);
    }

    #[test]
    fn test_chordangle_from_angle() {
        let angles = vec![
            Angle::from(Rad(0.)),
            Angle::from(Rad(1.)),
            Angle::from(Rad(-1.)),
            Angle::from(Rad(PI)),
        ];

        for angle in angles.into_iter() {
            let ca = ChordAngle::from(angle);
            let got = Angle::from(ca);
            assert_eq!(got, angle);
        }

        assert_eq!(STRAIGHT, ChordAngle::from(Angle::from(Rad(PI))));
        assert_eq!(Angle::inf(), Angle::from(ChordAngle::from(Angle::inf())));
    }

    fn chordangle_eq(a: ChordAngle, b: ChordAngle) {
        assert_f64_eq!(a.0, b.0);
    }

    #[test]
    fn test_chordangle_arithmetic() {
        let zero = ChordAngle::default();
        let deg_30 = ChordAngle::from(Deg(30.));
        let deg_60 = ChordAngle::from(Deg(60.));
        let deg_90 = ChordAngle::from(Deg(90.));
        let deg_120 = ChordAngle::from(Deg(120.));
        let deg_180 = STRAIGHT;

        chordangle_eq(zero + zero, zero);
        chordangle_eq(deg_60 + zero, deg_60);
        chordangle_eq(zero + deg_60, deg_60);
        chordangle_eq(deg_30 + deg_60, deg_90);
        chordangle_eq(deg_60 + deg_30, deg_90);
        chordangle_eq(deg_180 + zero, deg_180);
        chordangle_eq(deg_60 + deg_30, deg_90);
        chordangle_eq(deg_90 + deg_90, deg_180);
        chordangle_eq(deg_120 + deg_90, deg_180);
        chordangle_eq(deg_120 + deg_120, deg_180);
        chordangle_eq(deg_30 + deg_180, deg_180);
        chordangle_eq(deg_180 + deg_180, deg_180);

        chordangle_eq(zero - zero, zero);
        chordangle_eq(deg_60 - deg_60, zero);
        chordangle_eq(deg_180 - deg_180, zero);
        chordangle_eq(zero - deg_60, zero);
        chordangle_eq(deg_30 - deg_90, zero);
        chordangle_eq(deg_90 - deg_30, deg_60);
        chordangle_eq(deg_90 - deg_60, deg_30);
        chordangle_eq(deg_180 - zero, deg_180);
    }

    #[test]
    fn test_chordangle_trigonometry() {
        let iters = 40usize;
        for i in 0..(iters + 1) {
            let radians = PI * (i as f64) / (iters as f64);
            let chordangle = ChordAngle::from(Angle::from(Rad(radians)));

            assert_f64_eq!(radians.sin(), chordangle.sin());
            assert_f64_eq!(radians.cos(), chordangle.cos());

            // Since tan(x) is unbounded near pi/4, we map the result back to an
            // angle before comparing. The assertion is that the result is equal to
            // the tangent of a nearby angle.
            assert_f64_eq!(radians.tan().atan(), chordangle.tan().atan());
        }

        let angle_90 = ChordAngle::from_squared_length(2.);
        let angle_180 = ChordAngle::from_squared_length(4.);

        assert_f64_eq!(1., angle_90.sin());
        assert_f64_eq!(0., angle_90.cos());
        assert!(angle_90.tan().is_infinite());

        assert_f64_eq!(0., angle_180.sin());
        assert_f64_eq!(-1., angle_180.cos());
        assert_f64_eq!(0., angle_180.tan());
    }

    #[test]
    fn test_chordangle_expanded() {
        let zero = ChordAngle::default();
        assert_eq!(NEGATIVE.expanded(5.), NEGATIVE.expanded(5.));
        assert_eq!(ChordAngle::inf().expanded(-5.), ChordAngle::inf());
        assert_eq!(zero.expanded(-5.), zero);
        assert_eq!(
            ChordAngle::from_squared_length(1.25).expanded(0.25),
            ChordAngle::from_squared_length(1.5)
        );
        assert_eq!(
            ChordAngle::from_squared_length(0.75).expanded(0.25),
            ChordAngle::from_squared_length(1.)
        );
    }
}
