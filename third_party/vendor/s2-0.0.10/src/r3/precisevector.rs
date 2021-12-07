/*
Copyright 2019 Alexander Haynes. All rights reserved.

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

use crate::r3;
use bigdecimal;
use bigdecimal::ToPrimitive;
use std::str::FromStr;

pub fn prec_str(s: String) -> bigdecimal::BigDecimal {
    let f = bigdecimal::BigDecimal::from_str(&s).unwrap();
    return f;
}

pub fn prec_int(i: i64) -> bigdecimal::BigDecimal {
    return bigdecimal::BigDecimal::from(i);
}

pub fn prec_float(f: f64) -> bigdecimal::BigDecimal {
    return bigdecimal::BigDecimal::from(f);
}

/// PreciseVector represents a point in ℝ³ using high-precision values.
/// Note that this is NOT a complete implementation because there are some
/// operations that Vector supports that are not feasible with arbitrary precision
/// math. (e.g., methods that need divison like Normalize, or methods needing a
/// square root operation such as Norm)
#[derive(Clone, PartialEq, Eq, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct PreciseVector {
    x: bigdecimal::BigDecimal,
    y: bigdecimal::BigDecimal,
    z: bigdecimal::BigDecimal,
}

impl From<r3::vector::Vector> for PreciseVector {
    fn from(v: r3::vector::Vector) -> Self {
        PreciseVector::new(v.x, v.y, v.z)
    }
}

impl Into<r3::vector::Vector> for PreciseVector {
    fn into(self) -> r3::vector::Vector {
        // The accuracy flag is ignored on these conversions back to float64.
        let x = self.x.to_f64().unwrap();
        let y = self.y.to_f64().unwrap();
        let z = self.z.to_f64().unwrap();
        r3::vector::Vector { x, y, z }.normalize()
    }
}

impl PreciseVector {
    /// Creates a high precision vector from the given floating point values.
    fn new(x: f64, y: f64, z: f64) -> PreciseVector {
        PreciseVector {
            x: prec_float(x),
            y: prec_float(y),
            z: prec_float(z),
        }
    }

    /// norm2 returns the square of the norm.
    pub fn norm2(&self) -> bigdecimal::BigDecimal {
        self.dot(self.clone())
    }

    /// is_unit reports whether this vector is of unit length.
    pub fn is_unit(&self) -> bool {
        self.norm2() == prec_int(1_i64)
    }

    /// abs returns the vector with nonnegative components.
    pub fn abs(&self) -> PreciseVector {
        PreciseVector {
            x: bigdecimal::BigDecimal::abs(&self.x),
            y: bigdecimal::BigDecimal::abs(&self.y),
            z: bigdecimal::BigDecimal::abs(&self.z),
        }
    }
}

impl std::ops::Add<PreciseVector> for PreciseVector {
    type Output = PreciseVector;
    /// add returns the standard vector sum of v and ov.
    fn add(self, other: Self) -> Self {
        PreciseVector {
            x: self.x + other.x,
            y: self.y + other.y,
            z: self.z + other.z,
        }
    }
}

impl std::ops::Sub<PreciseVector> for PreciseVector {
    type Output = PreciseVector;
    /// sub returns the standard vector difference of v and ov.
    fn sub(self, other: Self) -> Self {
        PreciseVector {
            x: self.x - other.x,
            y: self.y - other.y,
            z: self.z - other.z,
        }
    }
}

impl std::ops::Mul<bigdecimal::BigDecimal> for PreciseVector {
    type Output = PreciseVector;
    /// mul returns the standard scalar product of v and f.
    fn mul(self, other: bigdecimal::BigDecimal) -> Self {
        PreciseVector {
            x: self.x * &other,
            y: self.y * &other,
            z: self.z * &other,
        }
    }
}

impl std::ops::Mul<f64> for PreciseVector {
    type Output = PreciseVector;
    /// mul returns the standard scalar product of v and f.
    fn mul(self, other: f64) -> Self {
        self * prec_float(other)
    }
}

impl PreciseVector {
    /// dot returns the standard dot product of v and ov.
    pub fn dot(&self, ov: PreciseVector) -> bigdecimal::BigDecimal {
        let a = self.clone();
        let b = ov.clone();
        return (a.x * b.x) + (a.y * b.y) + (a.z * b.z);
    }

    /// cross returns the standard cross product of v and ov.
    pub fn cross(&self, ov: PreciseVector) -> PreciseVector {
        return PreciseVector {
            x: (&self.y * &ov.z) - (&self.z * &ov.y),
            y: (&self.z * &ov.x) - (&self.x * &ov.z),
            z: (&self.x * &ov.y) - (&self.y * &ov.x),
        };
    }

    /// largest_component returns the axis that represents the largest component in this vector.
    pub fn largest_component(&self) -> r3::vector::Axis {
        let a = self.abs();
        if a.x > a.y {
            if a.x > a.z {
                r3::vector::Axis::X
            } else {
                r3::vector::Axis::Z
            }
        } else {
            if a.y > a.z {
                r3::vector::Axis::Y
            } else {
                r3::vector::Axis::Z
            }
        }
    }

    /// smallest_component returns the axis that represents the smallest component in this vector.
    pub fn smallest_component(&self) -> r3::vector::Axis {
        let t = self.abs();
        if t.x < t.y {
            if t.x < t.z {
                r3::vector::Axis::X
            } else {
                r3::vector::Axis::Z
            }
        } else {
            if t.y < t.z {
                r3::vector::Axis::Y
            } else {
                r3::vector::Axis::Z
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::consts::EPSILON;
    use r3::precisevector;
    use r3::vector::Axis;
    use r3::vector::Vector;

    fn pv(x: f64, y: f64, z: f64) -> PreciseVector {
        PreciseVector::new(x, y, z)
    }

    pub fn test_precise_round_trip_case(x: f64, y: f64, z: f64) {
        const EPSILON: f64 = 0.0000000000001;
        let pvn: Vector = PreciseVector::from(Vector { x, y, z }).into();
        let nvn = Vector { x, y, z }.normalize();
        assert!((pvn.x - nvn.x).abs() <= EPSILON);
        assert!((pvn.y - nvn.y).abs() <= EPSILON);
        assert!((pvn.z - nvn.z).abs() <= EPSILON);
    }

    #[test]
    pub fn test_precise_round_trip() {
        test_precise_round_trip_case(0.0, 0.0, 0.0);
        test_precise_round_trip_case(1.0, 2.0, 3.0);
        test_precise_round_trip_case(3.0, -4.0, 12.0);
        test_precise_round_trip_case(1.0, 1e-16, 1e-32);
    }

    #[test]
    pub fn test_precise_is_unit() {
        assert!(pv(0.0, 0.0, 0.0).is_unit() == false);
        assert!(pv(1.0, 0.0, 0.0).is_unit() == true);
        assert!(pv(0.0, 1.0, 0.0).is_unit() == true);
        assert!(pv(0.0, 0.0, 1.0).is_unit() == true);
        assert!(pv(1.0 + 2.0 * EPSILON, 0.0, 0.0).is_unit() == false);
        assert!(pv(0.0 * (1.0 + EPSILON), 0.0, 0.0).is_unit() == false);
        assert!(pv(1.0, 1.0, 1.0).is_unit() == false);
    }

    #[test]
    pub fn test_precise_norm2() {
        assert!(pv(0.0, 0.0, 0.0).norm2() == precisevector::prec_float(0.0));
        assert!(pv(0.0, 1.0, 0.0).norm2() == precisevector::prec_float(1.0));
        assert!(pv(1.0, 1.0, 1.0).norm2() == precisevector::prec_float(3.0));
        assert!(pv(1.0, 2.0, 3.0).norm2() == precisevector::prec_float(14.0));
        assert!(pv(3.0, -4.0, 12.0).norm2() == precisevector::prec_float(169.0));
    }

    #[test]
    pub fn test_precise_add() {
        assert_eq!(pv(0.0, 0.0, 0.0) + pv(0.0, 0.0, 0.0), pv(0.0, 0.0, 0.0));
        assert_eq!(pv(1.0, 0.0, 0.0) + pv(0.0, 0.0, 0.0), pv(1.0, 0.0, 0.0));
        assert_eq!(pv(1.0, 2.0, 3.0) + pv(4.0, 5.0, 7.0), pv(5.0, 7.0, 10.0));
        assert_eq!(
            pv(1.0, -3.0, 5.0) + pv(1.0, -6.0, -6.0),
            pv(2.0, -9.0, -1.0)
        );
    }

    #[test]
    pub fn test_precise_sub() {
        assert_eq!(pv(0.0, 0.0, 0.0) - pv(0.0, 0.0, 0.0), pv(0.0, 0.0, 0.0));
        assert_eq!(pv(1.0, 0.0, 0.0) - pv(0.0, 0.0, 0.0), pv(1.0, 0.0, 0.0));
        assert_eq!(pv(1.0, 2.0, 3.0) - pv(4.0, 5.0, 7.0), pv(-3.0, -3.0, -4.0));
        assert_eq!(pv(1.0, -3.0, 5.0) - pv(1.0, -6.0, -6.0), pv(0.0, 3.0, 11.0));
    }

    #[test]
    pub fn test_precise_mul() {
        assert_eq!(
            pv(0.0, 0.0, 0.0) * precisevector::prec_float(3.0),
            pv(0.0, 0.0, 0.0)
        );
        assert_eq!(
            pv(1.0, 0.0, 0.0) * precisevector::prec_float(1.0),
            pv(1.0, 0.0, 0.0)
        );
        assert_eq!(
            pv(1.0, 0.0, 0.0) * precisevector::prec_float(0.0),
            pv(0.0, 0.0, 0.0)
        );
        assert_eq!(
            pv(1.0, 0.0, 0.0) * precisevector::prec_float(3.0),
            pv(3.0, 0.0, 0.0)
        );
        assert_eq!(
            pv(1.0, -3.0, 5.0) * precisevector::prec_float(-1.0),
            pv(-1.0, 3.0, -5.0)
        );
        assert_eq!(
            pv(1.0, -3.0, 5.0) * precisevector::prec_float(2.0),
            pv(2.0, -6.0, 10.0)
        );
    }

    #[test]
    pub fn test_precise_mul_by_f64() {
        assert_eq!(pv(0.0, 0.0, 0.0) * 3.0, pv(0.0, 0.0, 0.0));
        assert_eq!(pv(1.0, 0.0, 0.0) * 1.0, pv(1.0, 0.0, 0.0));
        assert_eq!(pv(1.0, 0.0, 0.0) * 0.0, pv(0.0, 0.0, 0.0));
        assert_eq!(pv(1.0, 0.0, 0.0) * 3.0, pv(3.0, 0.0, 0.0));
        assert_eq!(pv(1.0, -3.0, 5.0) * -1.0, pv(-1.0, 3.0, -5.0));
        assert_eq!(pv(1.0, -3.0, 5.0) * 2.0, pv(2.0, -6.0, 10.0));
    }

    #[test]
    pub fn test_precise_dot() {
        assert_eq!(
            pv(1.0, 0.0, 0.0).dot(pv(1.0, 0.0, 0.0)),
            precisevector::prec_float(1.0)
        );
        assert_eq!(
            pv(0.0, 1.0, 0.0).dot(pv(0.0, 1.0, 0.0)),
            precisevector::prec_float(1.0)
        );
        assert_eq!(
            pv(0.0, 0.0, 1.0).dot(pv(0.0, 0.0, 1.0)),
            precisevector::prec_float(1.0)
        );
        assert_eq!(
            pv(1.0, 0.0, 0.0).dot(pv(0.0, 1.0, 0.0)),
            precisevector::prec_float(0.0)
        );
        assert_eq!(
            pv(1.0, 0.0, 0.0).dot(pv(0.0, 1.0, 1.0)),
            precisevector::prec_float(0.0)
        );
        assert_eq!(
            pv(1.0, 1.0, 1.0).dot(pv(-1.0, -1.0, -1.0)),
            precisevector::prec_float(-3.0)
        );
    }

    #[test]
    pub fn test_precise_cross() {
        assert_eq!(
            pv(1.0, 0.0, 0.0).cross(pv(1.0, 0.0, 0.0)),
            pv(0.0, 0.0, 0.0)
        );
        assert_eq!(
            pv(1.0, 0.0, 0.0).cross(pv(0.0, 1.0, 0.0)),
            pv(0.0, 0.0, 1.0)
        );
        assert_eq!(
            pv(0.0, 1.0, 0.0).cross(pv(0.0, 0.0, 1.0)),
            pv(1.0, 0.0, 0.0)
        );
        assert_eq!(
            pv(0.0, 0.0, 1.0).cross(pv(1.0, 0.0, 0.0)),
            pv(0.0, 1.0, 0.0)
        );
        assert_eq!(
            pv(0.0, 1.0, 0.0).cross(pv(1.0, 0.0, 0.0)),
            pv(0.0, 0.0, -1.0)
        );
        assert_eq!(
            pv(1.0, 2.0, 3.0).cross(pv(-4.0, 5.0, -6.0)),
            pv(-27.0, -6.0, 13.0)
        );
    }

    fn test_precise_identities_case(v1: PreciseVector, v2: PreciseVector) {
        let c1 = v1.cross(v2.clone());
        let c2 = v2.cross(v1.clone());
        let d1 = v1.dot(v2.clone());
        let d2 = v2.dot(v1.clone());
        assert_eq!(d1, d2);
        assert_eq!(c1, c2 * -1.0);
        assert_eq!(v1.dot(c1.clone()), precisevector::prec_float(0.0));
        assert_eq!(v2.dot(c1.clone()), precisevector::prec_float(0.0));
    }

    #[test]
    pub fn test_precise_identities() {
        let v1 = pv(0.0, 0.0, 0.0);
        let v2 = pv(0.0, 0.0, 0.0);
        test_precise_identities_case(v1, v2);

        let v1 = pv(0.0, 0.0, 0.0);
        let v2 = pv(0.0, 1.0, 2.0);
        test_precise_identities_case(v1, v2);

        let v1 = pv(1.0, 0.0, 0.0);
        let v2 = pv(0.0, 1.0, 0.0);
        test_precise_identities_case(v1, v2);

        let v1 = pv(1.0, 0.0, 0.0);
        let v2 = pv(0.0, 1.0, 1.0);
        test_precise_identities_case(v1, v2);

        let v1 = pv(1.0, 1.0, 1.0);
        let v2 = pv(-1.0, -1.0, -1.0);
        test_precise_identities_case(v1, v2);

        let v1 = pv(1.0, 2.0, 2.0);
        let v2 = pv(-0.3, 0.4, -1.2);
        test_precise_identities_case(v1, v2);
    }

    #[test]
    pub fn test_precise_largest_smallest_components() {
        let v1 = pv(0.0, 0.0, 0.0);
        assert_eq!(v1.largest_component(), Axis::Z);
        assert_eq!(v1.smallest_component(), Axis::Z);
        let v1 = pv(1.0, 0.0, 0.0);
        assert_eq!(v1.largest_component(), Axis::X);
        assert_eq!(v1.smallest_component(), Axis::Z);
        let v1 = pv(1.0, -1.0, 0.0);
        assert_eq!(v1.largest_component(), Axis::Y);
        assert_eq!(v1.smallest_component(), Axis::Z);
        let v1 = pv(-1.0, -1.1, -1.1);
        assert_eq!(v1.largest_component(), Axis::Z);
        assert_eq!(v1.smallest_component(), Axis::X);
        let v1 = pv(0.5, -0.4, -0.5);
        assert_eq!(v1.largest_component(), Axis::Z);
        assert_eq!(v1.smallest_component(), Axis::Y);
        let v1 = pv(1e-15, 1e-14, 1e-13);
        assert_eq!(v1.largest_component(), Axis::Z);
        assert_eq!(v1.smallest_component(), Axis::X);
    }
}
