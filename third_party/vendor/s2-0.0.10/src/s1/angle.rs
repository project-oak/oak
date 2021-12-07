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

/// Angle represents a 1D angle. The internal representation is a double precision
/// value in radians, so conversion to and from radians is exact.
/// Conversions between E5, E6, E7, and Degrees are not always
/// exact. For example, Deg(3.1) is different from E6(3100000) or E7(310000000).
///
///     use s2::s1::angle::*;
///     use std::f64::consts::PI;
///
///     // The following conversions between degrees and radians are exact:
///     assert_eq!(Deg(180.), Deg::from(Rad(PI)));
///     for n in 0..9 {
///         // for n == 0..8
///         assert_eq!(Rad(PI/(n as f64)), Deg(180./(n as f64)).into());
///     }
///
///     // These identities hold when the arguments are scaled up or down by any power
///     // of 2. Some similar identities are also true, for example,
///     assert_eq!(Rad(PI/3.), Deg(60.).into());
///
///     // But be aware that this type of identity does not hold in general. For example,
///     assert_ne!(Rad(PI/60.), Deg(3.).into());
///
///     // Similarly, the conversion to radians means that Deg::from(Angle::from(Deg(x)))
///     // does not always equal x. For example,
///
///     // for n == 0..8
///     for n in 0..9 {
///         let x = 45. * (n as f64);
///         assert_eq!(Deg(x), Deg::from(Angle::from(Deg(x))));
///     }
///
///     // but
///     assert_ne!(Deg(60.), Deg::from(Angle::from(Deg(60.))));
///
/// When testing for equality, you should allow for numerical errors (float64Eq)
/// or convert to discrete E5/E6/E7 values first.
#[derive(Clone, Copy, PartialEq, PartialOrd)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Angle(f64);
#[derive(Clone, Copy, PartialEq, PartialOrd, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Rad(pub f64);
#[derive(Clone, Copy, PartialEq, PartialOrd, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Deg(pub f64);

#[derive(Clone, Copy, PartialEq, PartialOrd, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct E5(pub i32);
#[derive(Clone, Copy, PartialEq, PartialOrd, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct E6(pub i32);
#[derive(Clone, Copy, PartialEq, PartialOrd, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct E7(pub i32);

impl Angle {
    /// rad returns the angle in radians.
    pub fn rad(&self) -> f64 {
        self.0
    }

    /// deg returns the angle in degrees.
    pub fn deg(&self) -> f64 {
        Deg::from(self).0
    }

    /// inf returns an angle larger than any finite angle.
    pub fn inf() -> Self {
        Angle(std::f64::INFINITY)
    }

    /// is_infinite reports whether this Angle is infinite.
    pub fn is_infinite(&self) -> bool {
        self.0.is_infinite()
    }

    /// abs returns the absolute value of the angle.
    pub fn abs(&self) -> Self {
        Angle(self.0.abs())
    }

    /// normalized returns an equivalent angle in [0, 2π).
    pub fn normalized(&self) -> Self {
        let rem = self.0 % (2f64 * PI);
        if rem < 0. {
            Angle(rem + 2f64 * PI)
        } else {
            Angle(rem)
        }
    }
}

impl std::ops::Mul<f64> for Angle {
    type Output = Self;
    fn mul(self, other: f64) -> Self {
        Angle(self.0 * other)
    }
}
impl std::ops::Add<f64> for Angle {
    type Output = Self;
    fn add(self, other: f64) -> Self {
        Angle(self.0 + other)
    }
}

impl std::fmt::Debug for Angle {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:.7}", Deg::from(self).0)
    }
}

macro_rules! convert {
    ($tyname1:ident, $tyname2:ident, $mul:expr) => {
        impl From<$tyname1> for $tyname2 {
            fn from(a: $tyname1) -> Self {
                $tyname2(a.0 * $mul)
            }
        }
        impl<'a> From<&'a $tyname1> for $tyname2 {
            fn from(a: &$tyname1) -> Self {
                $tyname2(a.0 * $mul)
            }
        }
        impl From<$tyname2> for $tyname1 {
            fn from(a: $tyname2) -> Self {
                $tyname1(a.0 / $mul)
            }
        }
        impl<'a> From<&'a $tyname2> for $tyname1 {
            fn from(a: &$tyname2) -> Self {
                $tyname1(a.0 / $mul)
            }
        }
    };
}

macro_rules! convert_i32 {
    ($tyname1:ident, $tyname2:ident, $mul:expr) => {
        impl From<$tyname1> for $tyname2 {
            fn from(a: $tyname1) -> Self {
                $tyname2(f64::from(a.0) * $mul)
            }
        }
        impl<'a> From<&'a $tyname1> for $tyname2 {
            fn from(a: &$tyname1) -> Self {
                $tyname2(f64::from(a.0) * $mul)
            }
        }
        impl From<$tyname2> for $tyname1 {
            fn from(a: $tyname2) -> Self {
                $tyname1((a.0 / $mul).round() as i32)
            }
        }
        impl<'a> From<&'a $tyname2> for $tyname1 {
            fn from(a: &$tyname2) -> Self {
                $tyname1((a.0 / $mul).round() as i32)
            }
        }
    };
}

convert!(Rad, Angle, 1.);
convert!(Deg, Rad, PI / 180.);
convert!(Deg, Angle, PI / 180.);

convert_i32!(E5, Angle, PI / 180. / 1e5);
convert_i32!(E6, Angle, PI / 180. / 1e6);
convert_i32!(E7, Angle, PI / 180. / 1e7);

convert_i32!(E5, Deg, 1. / 1e5);
convert_i32!(E6, Deg, 1. / 1e6);
convert_i32!(E7, Deg, 1. / 1e7);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::consts::*;

    #[test]
    fn test_deg_rad() {
        let deg = Deg(180.);
        let rad = Angle(PI);
        assert_eq!(rad, deg.clone().into());
        assert_eq!(deg, rad.clone().into());
    }

    #[test]
    fn test_empty_value() {
        assert_eq!(Deg::from(Angle(0.)).0, 0.);
    }

    #[test]
    fn test_pi_radians_exactly_180_degrees() {
        assert_eq!(Angle(PI).rad(), PI);
        assert_eq!(Angle(PI).deg(), 180.);

        assert_eq!(Angle::from(Deg(180.)).rad(), PI);
        assert_eq!(Angle::from(Deg(180.)).deg(), 180.);

        assert_eq!(Angle(PI / 2.).deg(), 90.);

        assert_eq!(Angle(PI / -2.).deg(), -90.);
        assert_eq!(Angle::from(Deg(-45.)).rad(), PI / -4.);
    }

    fn test_rounding(have: f64, want: i32) {
        assert_eq!(E5::from(Deg(have * 1e-5)).0, want);
        assert_eq!(E6::from(Deg(have * 1e-6)).0, want);
        assert_eq!(E7::from(Deg(have * 1e-7)).0, want);
    }

    #[test]
    fn test_e5e6e7_representation() {
        // NOTE(dsymonds): This first test gives a variance in the 16th decimal place. I should track that down.
        assert_f64_eq!(Angle::from(Deg(-45.)).0, Angle::from(E5(-4500000)).0);

        assert_eq!(Angle::from(Deg(-60.)), Angle::from(E6(-60000000)));
        assert_eq!(Angle::from(Deg(-75.)), Angle::from(E7(-750000000)));

        assert_eq!(-17256123, E5::from(Angle::from(Deg(-172.56123))).0);
        assert_eq!(12345678, E6::from(Angle::from(Deg(12.345678))).0);
        assert_eq!(-123456789, E7::from(Angle::from(Deg(-12.3456789))).0);

        test_rounding(0.500000001, 1);
        test_rounding(-0.500000001, -1);
        test_rounding(0.499999999, 0);
        test_rounding(-0.499999999, 0);
    }

    #[test]
    fn test_normalize_correctly_canonicalize_angles() {
        assert_eq!(Angle::from(Deg(0.)), Angle::from(Deg(360.)).normalized());
        assert_eq!(Angle::from(Deg(180.)), Angle::from(Deg(-180.)).normalized());
        assert_eq!(Angle::from(Deg(180.)), Angle::from(Deg(180.)).normalized());
        assert_eq!(Angle::from(Deg(180.)), Angle::from(Deg(540.)).normalized());
        assert_eq!(Angle::from(Deg(90.)), Angle::from(Deg(-270.)).normalized());
    }

    #[test]
    fn test_degrees_vs_radians() {
        // This test tests the exactness of specific values between degrees and radians.
        let mut k = -8.;
        while k <= 8. {
            assert_eq!(Deg(45. * k), Deg::from(Angle(k * PI / 4.)));
            assert_eq!(Angle::from(Deg(45. * k)), Angle(k * PI / 4.));
            k += 1.;
        }

        for k in 0..30 {
            let n = (1i32 << k) as f64;
            assert_eq!(Angle::from(Deg(180. / n)), Angle(PI / (1. * n)));
            assert_eq!(Angle::from(Deg(60. / n)), Angle(PI / (3. * n)));
            assert_eq!(Angle::from(Deg(36. / n)), Angle(PI / (5. * n)));
            assert_eq!(Angle::from(Deg(20. / n)), Angle(PI / (9. * n)));
            assert_eq!(Angle::from(Deg(4. / n)), Angle(PI / (45. * n)));
        }

        // We also spot check a non-identity.
        assert_f64_eq!(Deg::from(Angle::from(Deg(60.))).0, Deg(60.).0);
    }
}

// BUG(dsymonds): The major differences from the C++ version are:
//   - no unsigned E5/E6/E7 methods
//   - no S2Point or S2LatLng constructors
//   - no comparison or arithmetic operators
