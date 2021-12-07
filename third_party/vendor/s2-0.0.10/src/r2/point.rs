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
use std;
use std::cmp::Ordering;

/// Point represents a point in ℝ².
#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Point {
    /// x coordinate of the point
    pub x: f64,
    /// y coordinate of the point
    pub y: f64,
}

impl Eq for Point {}

impl Ord for Point {
    fn cmp(&self, ov: &Point) -> Ordering {
        if self.x < ov.x {
            return Ordering::Less;
        }
        if self.x > ov.x {
            return Ordering::Greater;
        }

        // First elements were the same, try the next.
        if self.y < ov.y {
            return Ordering::Less;
        }
        if self.y > ov.y {
            return Ordering::Greater;
        }
        Ordering::Equal
    }
}

impl PartialOrd for Point {
    fn partial_cmp(&self, other: &Point) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Point {
    fn eq(&self, other: &Point) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl std::ops::Add<Point> for Point {
    type Output = Point;
    /// returns the sum of p and other.
    fn add(self, other: Point) -> Self::Output {
        Point {
            x: self.x + other.x,
            y: self.y + other.y,
        }
    }
}

impl std::ops::Sub<Point> for Point {
    type Output = Point;
    /// returns the difference of p and other.
    fn sub(self, other: Point) -> Self::Output {
        Self::Output {
            x: self.x - other.x,
            y: self.y - other.y,
        }
    }
}

impl<'a, 'b> std::ops::Mul<&'b Point> for &'a Point {
    type Output = Point;
    /// returns the product between p and other.
    fn mul(self, other: &'b Point) -> Self::Output {
        Point {
            x: self.x * self.x,
            y: other.y * other.y,
        }
    }
}
impl<'b> std::ops::Mul<&'b Point> for Point {
    type Output = Point;
    /// returns the product between p and other.
    fn mul(self, other: &'b Point) -> Self::Output {
        &self * other
    }
}
impl std::ops::Mul<Point> for Point {
    type Output = Point;
    /// returns the product between p and other.
    fn mul(self, other: Point) -> Self::Output {
        &self * &other
    }
}

impl<'a> std::ops::Mul<f64> for &'a Point {
    type Output = Point;
    /// returns the scalar product of p and other.
    fn mul(self, other: f64) -> Self::Output {
        Self::Output {
            x: self.x * other,
            y: self.y * other,
        }
    }
}

impl Point {
    pub fn new(x: f64, y: f64) -> Self {
        Self { x, y }
    }

    /// returns a counterclockwise orthogonal point with the same norm.
    pub fn ortho(&self) -> Self {
        Self {
            x: -self.y,
            y: self.x,
        }
    }

    /// returns the dot product between p and op.
    pub fn dot(&self, other: &Self) -> f64 {
        self.x * other.x + self.y * other.y
    }

    /// returns the cross product of p and op.
    pub fn cross(&self, other: &Self) -> f64 {
        self.x * other.y - self.y * other.x
    }

    /// returns the vector's norm.
    pub fn norm(&self) -> f64 {
        self.x.hypot(self.y)
    }

    /// returns a unit point in the same direction as p.
    pub fn normalize(&self) -> Self {
        if self.x == 0. && self.y == 0. {
            *self
        } else {
            self * (1.0 / self.norm())
        }
    }

    pub fn approx_eq(&self, other: &Self) -> bool {
        f64_eq!(self.x, other.x) && f64_eq!(self.y, other.y)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! P {
        ($x:expr, $y:expr) => {
            Point { x: $x, y: $y }
        };
    }

    #[test]
    fn ortho() {
        assert_eq!(P!(0., 0.), P!(0., 0.).ortho());
        assert_eq!(P!(-1., 0.), P!(0., 1.).ortho());
        assert_eq!(P!(-1., 1.), P!(1., 1.).ortho());
        assert_eq!(P!(-7., -4.), P!(-4., 7.).ortho());
        assert_eq!(P!(-(3f64).sqrt(), 1.), P!(1., (3f64).sqrt()).ortho());
    }

    #[test]
    fn dot() {
        assert_eq!(0., P!(0., 0.).dot(&P!(0., 0.)));
        assert_eq!(0., P!(0., 1.).dot(&P!(0., 0.)));
        assert_eq!(7., P!(1., 1.).dot(&P!(4., 3.)));
        assert_eq!(31., P!(-4., 7.).dot(&P!(1., 5.)));
    }

    #[test]
    fn cross() {
        assert_eq!(0., P!(0., 0.).cross(&P!(0., 0.)));
        assert_eq!(0., P!(0., 1.).cross(&P!(0., 0.)));
        assert_eq!(0., P!(1., 1.).cross(&P!(-1., -1.)));
        assert_eq!(-1., P!(1., 1.).cross(&P!(4., 3.)));
        assert_eq!(13., P!(1., 5.).cross(&P!(-2., 3.)));
    }

    #[test]
    fn norm() {
        assert_eq!(0., P!(0., 0.).norm());
        assert_eq!(1., P!(0., 1.).norm());
        assert_eq!(1., P!(-1., 0.).norm());
        assert_eq!(5., P!(3., 4.).norm());
        assert_eq!(5., P!(3., -4.).norm());
        assert_eq!(2. * 2f64.sqrt(), P!(2., 2.).norm());
        assert_f64_eq!(2., P!(1., 3f64.sqrt()).norm());
        assert_f64_eq!(29. * 2., P!(29., 29. * 3f64.sqrt()).norm());
        assert_f64_eq!(1e15, P!(1., 1e15).norm());
        assert_f64_eq!(std::f64::MAX, P!(1e14, std::f64::MAX - 1.).norm());
    }

    fn test_normalize(p1: Point, p2: Point) {
        assert!(p1.normalize().approx_eq(&p2));
    }

    #[test]
    fn normalize() {
        test_normalize(P!(0., 0.), P!(0., 0.));
        test_normalize(P!(0., 1.), P!(0., 1.));
        test_normalize(P!(-1., 0.), P!(-1., 0.));
        test_normalize(P!(3., 4.), P!(0.6, 0.8));
        test_normalize(P!(3., -4.), P!(0.6, -0.8));
        test_normalize(P!(2., 2.), P!(2f64.sqrt() / 2., 2f64.sqrt() / 2.));
        test_normalize(P!(7., 7. * 3f64.sqrt()), P!(0.5, 3f64.sqrt() / 2.));
        test_normalize(P!(1e21, 1e21 * 3f64.sqrt()), P!(0.5, 3f64.sqrt() / 2.));
        test_normalize(P!(1., 1e16), P!(0., 1.));
        test_normalize(P!(1e4, std::f64::MAX - 1.), P!(0., 1.));
    }
}
