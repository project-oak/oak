/*
Copyright 2016 Google Inc. All rights reserved.
Copyright 2017 Jhyun Yu. All rights reserved.

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

//! This file contains various predicates that are guaranteed to produce
//! correct, consistent results. They are also relatively efficient. This is
//! achieved by computing conservative error bounds and falling back to high
//! precision or even exact arithmetic when the result is uncertain. Such
//! predicates are useful in implementing robust algorithms.
//!
//! See also EdgeCrosser, which implements various exact
//! edge-crossing predicates more efficiently than can be done here.

use crate::consts::*;
use crate::s2::point::Point;

/// MAX_DETERMINANT_ERROR is the maximum error in computing (AxB).C where all vectors
/// are unit length. Using standard inequalities, it can be shown that
///
///  fl(AxB) = AxB + D where |D| <= (|AxB| + (2/sqrt(3))*|A|*|B|) * e
///
/// where "fl()" denotes a calculation done in floating-point arithmetic,
/// |x| denotes either absolute value or the L2-norm as appropriate, and
/// e is a reasonably small value near the noise level of floating point
/// number accuracy. Similarly,
///
///  fl(B.C) = B.C + d where |d| <= (|B.C| + 2*|B|*|C|) * e .
///
/// Applying these bounds to the unit-length vectors A,B,C and neglecting
/// relative error (which does not affect the sign of the result), we get
///
///  fl((AxB).C) = (AxB).C + d where |d| <= (3 + 2/sqrt(3)) * e
const MAX_DETERMINANT_ERROR: f64 = 1.8274 * DBL_EPSILON;

/// DET_ERROR_MULTIPLIER is the factor to scale the magnitudes by when checking
/// for the sign of set of points with certainty. Using a similar technique to
/// the one used for MAX_DETERMINANT_ERROR, the error is at most:
///
///   |d| <= (3 + 6/sqrt(3)) * |A-C| * |B-C| * e
///
/// If the determinant magnitude is larger than this value then we know
/// its sign with certainty.
const DET_ERROR_MULTIPLIER: f64 = 3.2321 * DBL_EPSILON;

#[derive(PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Direction {
    Clockwise,
    Indeterminate,
    CounterClockwise,
}

/// sign returns true if the points A, B, C are strictly counterclockwise,
/// and returns false if the points are clockwise or collinear (i.e. if they are all
/// contained on some great circle).
///
/// Due to numerical errors, situations may arise that are mathematically
/// impossible, e.g. ABC may be considered strictly CCW while BCA is not.
/// However, the implementation guarantees the following:
///
/// If Sign(a,b,c), then !Sign(c,b,a) for all a,b,c.
pub fn sign(a: &Point, b: &Point, c: &Point) -> bool {
    // NOTE(dnadasi): In the C++ API the equivalent method here was known as "SimpleSign".

    // We compute the signed volume of the parallelepiped ABC. The usual
    // formula for this is (A ⨯ B) · C, but we compute it here using (C ⨯ A) · B
    // in order to ensure that ABC and CBA are not both CCW. This follows
    // from the following identities (which are true numerically, not just
    // mathematically):
    //
    //     (1) x ⨯ y == -(y ⨯ x)
    //     (2) -x · y == -(x · y)
    c.0.cross(&a.0).dot(&b.0) > 0f64
}

/// robust_sign returns a Direction representing the ordering of the points.
/// CounterClockwise is returned if the points are in counter-clockwise order,
/// Clockwise for clockwise, and Indeterminate if any two points are the same (collinear),
/// or the sign could not completely be determined.
///
/// This function has additional logic to make sure that the above properties hold even
/// when the three points are coplanar, and to deal with the limitations of
/// floating-point arithmetic.
///
/// RobustSign satisfies the following conditions:
///
///  (1) RobustSign(a,b,c) == Indeterminate if and only if a == b, b == c, or c == a
///  (2) RobustSign(b,c,a) == RobustSign(a,b,c) for all a,b,c
///  (3) RobustSign(c,b,a) == -RobustSign(a,b,c) for all a,b,c
///
/// In other words:
///
///  (1) The result is Indeterminate if and only if two points are the same.
///  (2) Rotating the order of the arguments does not affect the result.
///  (3) Exchanging any two arguments inverts the result.
///
/// On the other hand, note that it is not true in general that
/// RobustSign(-a,b,c) == -RobustSign(a,b,c), or any similar identities
/// involving antipodal points.
pub fn robust_sign(a: &Point, b: &Point, c: &Point) -> Direction {
    let sign = triage_sign(a, b, c);
    if sign == Direction::Indeterminate {
        expensive_sign(a, b, c)
    } else {
        sign
    }
}

/// stable_sign reports the direction sign of the points in a numerically stable way.
/// Unlike triageSign, this method can usually compute the correct determinant sign
/// even when all three points are as collinear as possible. For example if three
/// points are spaced 1km apart along a random line on the Earth's surface using
/// the nearest representable points, there is only a 0.4% chance that this method
/// will not be able to find the determinant sign. The probability of failure
/// decreases as the points get closer together; if the collinear points are 1 meter
/// apart, the failure rate drops to 0.0004%.
///
/// This method could be extended to also handle nearly-antipodal points, but antipodal
/// points are rare in practice so it seems better to simply fall back to
/// exact arithmetic in that case.
pub fn stable_sign(a: &Point, b: &Point, c: &Point) -> Direction {
    let ab = b.0 - a.0;
    let ab2 = ab.norm2();
    let bc = c.0 - b.0;
    let bc2 = bc.norm2();
    let ca = a.0 - c.0;
    let ca2 = ca.norm2();

    // Now compute the determinant ((A-C)x(B-C)).C, where the vertices have been
    // cyclically permuted if necessary so that AB is the longest edge. (This
    // minimizes the magnitude of cross product.)  At the same time we also
    // compute the maximum error in the determinant.

    // The two shortest edges, pointing away from their common point.
    let (e1, e2, op) = if ab2 >= bc2 && ab2 >= ca2 {
        // AB is the longest edge.
        (ca, bc, &c.0)
    } else if bc2 >= ca2 {
        // BC is the longest edge.
        (ab, ca, &a.0)
    } else {
        // CA is the longest edge.
        (bc, ab, &b.0)
    };

    let det = -1. * e1.cross(&e2).dot(&op);
    let max_err = DET_ERROR_MULTIPLIER * (e1.norm2() * e2.norm2()).sqrt();

    // If the determinant isn't zero, within maxErr, we know definitively the point ordering.
    if det > max_err {
        Direction::CounterClockwise
    } else if det < -max_err {
        Direction::Clockwise
    } else {
        Direction::Indeterminate
    }
}

/// triage_sign returns the direction sign of the points. It returns Indeterminate if two
/// points are identical or the result is uncertain. Uncertain cases can be resolved, if
/// desired, by calling expensiveSign.
///
/// The purpose of this method is to allow additional cheap tests to be done without
/// calling expensiveSign.
pub fn triage_sign(a: &Point, b: &Point, c: &Point) -> Direction {
    let det = a.0.cross(&b.0).dot(&c.0);
    if det > MAX_DETERMINANT_ERROR {
        Direction::CounterClockwise
    } else if det < -MAX_DETERMINANT_ERROR {
        Direction::Clockwise
    } else {
        Direction::Indeterminate
    }
}

/// expensive_sign reports the direction sign of the points. It returns Indeterminate
/// if two of the input points are the same. It uses multiple-precision arithmetic
/// to ensure that its results are always self-consistent.
fn expensive_sign(a: &Point, b: &Point, c: &Point) -> Direction {
    // Return Indeterminate if and only if two points are the same.
    // This ensures RobustSign(a,b,c) == Indeterminate if and only if a == b, b == c, or c == a.
    // ie. Property 1 of RobustSign.
    if a == b || b == c || c == a {
        return Direction::Indeterminate;
    }

    // Next we try recomputing the determinant still using floating-point
    // arithmetic but in a more precise way. This is more expensive than the
    // simple calculation done by triageSign, but it is still *much* cheaper
    // than using arbitrary-precision arithmetic. This optimization is able to
    // compute the correct determinant sign in virtually all cases except when
    // the three points are truly collinear (e.g., three points on the equator).
    let det_sign = stable_sign(a, b, c);
    if det_sign != Direction::Indeterminate {
        det_sign
    } else {
        // Otherwise fall back to exact arithmetic and symbolic permutations.
        exact_sign(a, b, c, false)
    }
}

/// exact-sign reports the direction sign of the points using exact precision arithmetic.
fn exact_sign(_: &Point, _: &Point, _: &Point, _: bool) -> Direction {
    // In the C++ version, the final computation is performed using OpenSSL's
    // Bignum exact precision math library. The existence of an equivalent
    // library in Go is indeterminate. In C++, using the exact precision library
    // to solve this stage is ~300x slower than the above checks.
    // TODO(roberts): Select and incorporate an appropriate Go exact precision
    // floating point library for the remaining calculations.
    Direction::Indeterminate
}

/*
package s2

import (
    "math"
    "testing"

    "github.com/golang/geo/r3"
)

func TestPredicatesSign(t *testing.T) {
    tests := []struct {
        p1x, p1y, p1z, p2x, p2y, p2z, p3x, p3y, p3z float64
        want                                        bool
    }{
        {1, 0, 0, 0, 1, 0, 0, 0, 1, true},
        {0, 1, 0, 0, 0, 1, 1, 0, 0, true},
        {0, 0, 1, 1, 0, 0, 0, 1, 0, true},
        {1, 1, 0, 0, 1, 1, 1, 0, 1, true},
        {-3, -1, 4, 2, -1, -3, 1, -2, 0, true},

        // All degenerate cases of Sign(). Let M_1, M_2, ... be the sequence of
        // submatrices whose determinant sign is tested by that function. Then the
        // i-th test below is a 3x3 matrix M (with rows A, B, C) such that:
        //
        //    det(M) = 0
        //    det(M_j) = 0 for j < i
        //    det(M_i) != 0
        //    A < B < C in lexicographic order.
        // det(M_1) = b0*c1 - b1*c0
        {-3, -1, 0, -2, 1, 0, 1, -2, 0, false},
        // det(M_2) = b2*c0 - b0*c2
        {-6, 3, 3, -4, 2, -1, -2, 1, 4, false},
        // det(M_3) = b1*c2 - b2*c1
        {0, -1, -1, 0, 1, -2, 0, 2, 1, false},
        // From this point onward, B or C must be zero, or B is proportional to C.
        // det(M_4) = c0*a1 - c1*a0
        {-1, 2, 7, 2, 1, -4, 4, 2, -8, false},
        // det(M_5) = c0
        {-4, -2, 7, 2, 1, -4, 4, 2, -8, false},
        // det(M_6) = -c1
        {0, -5, 7, 0, -4, 8, 0, -2, 4, false},
        // det(M_7) = c2*a0 - c0*a2
        {-5, -2, 7, 0, 0, -2, 0, 0, -1, false},
        // det(M_8) = c2
        {0, -2, 7, 0, 0, 1, 0, 0, 2, false},
    }

    for _, test := range tests {
        p1 := Point{r3.Vector{test.p1x, test.p1y, test.p1z}}
        p2 := Point{r3.Vector{test.p2x, test.p2y, test.p2z}}
        p3 := Point{r3.Vector{test.p3x, test.p3y, test.p3z}}
        result := Sign(p1, p2, p3)
        if result != test.want {
            t.Errorf("Sign(%v, %v, %v) = %v, want %v", p1, p2, p3, result, test.want)
        }
        if test.want {
            // For these cases we can test the reversibility condition
            result = Sign(p3, p2, p1)
            if result == test.want {
                t.Errorf("Sign(%v, %v, %v) = %v, want %v", p3, p2, p1, result, !test.want)
            }
        }
    }
}

// Points used in the various RobustSign tests.
var (
    // The following points happen to be *exactly collinear* along a line that it
    // approximate tangent to the surface of the unit sphere. In fact, C is the
    // exact midpoint of the line segment AB. All of these points are close
    // enough to unit length to satisfy r3.Vector.IsUnit().
    poA = Point{r3.Vector{0.72571927877036835, 0.46058825605889098, 0.51106749730504852}}
    poB = Point{r3.Vector{0.7257192746638208, 0.46058826573818168, 0.51106749441312738}}
    poC = Point{r3.Vector{0.72571927671709457, 0.46058826089853633, 0.51106749585908795}}

    // The points "x1" and "x2" are exactly proportional, i.e. they both lie
    // on a common line through the origin. Both points are considered to be
    // normalized, and in fact they both satisfy (x == x.Normalize()).
    // Therefore the triangle (x1, x2, -x1) consists of three distinct points
    // that all lie on a common line through the origin.
    x1 = Point{r3.Vector{0.99999999999999989, 1.4901161193847655e-08, 0}}
    x2 = Point{r3.Vector{1, 1.4901161193847656e-08, 0}}

    // Here are two more points that are distinct, exactly proportional, and
    // that satisfy (x == x.Normalize()).
    x3 = Point{r3.Vector{1, 1, 1}.Normalize()}
    x4 = Point{x3.Mul(0.99999999999999989)}

    // The following three points demonstrate that Normalize() is not idempotent, i.e.
    // y0.Normalize() != y0.Normalize().Normalize(). Both points are exactly proportional.
    y0 = Point{r3.Vector{1, 1, 0}}
    y1 = Point{y0.Normalize()}
    y2 = Point{y1.Normalize()}
)

func TestPredicatesRobustSignEqualities(t *testing.T) {
    tests := []struct {
        p1, p2 Point
        want   bool
    }{
        {Point{poC.Sub(poA.Vector)}, Point{poB.Sub(poC.Vector)}, true},
        {x1, Point{x1.Normalize()}, true},
        {x2, Point{x2.Normalize()}, true},
        {x3, Point{x3.Normalize()}, true},
        {x4, Point{x4.Normalize()}, true},
        {x3, x4, false},
        {y1, y2, false},
        {y2, Point{y2.Normalize()}, true},
    }

    for _, test := range tests {
        if got := test.p1.Vector == test.p2.Vector; got != test.want {
            t.Errorf("Testing equality for RobustSign. %v = %v, got %v want %v", test.p1, test.p2, got, test.want)
        }
    }
}

func TestPredicatesRobustSign(t *testing.T) {
    x := Point{r3.Vector{1, 0, 0}}
    y := Point{r3.Vector{0, 1, 0}}
    z := Point{r3.Vector{0, 0, 1}}

    tests := []struct {
        p1, p2, p3 Point
        want       Direction
    }{
        // Simple collinear points test cases.
        // a == b != c
        {x, x, z, Indeterminate},
        // a != b == c
        {x, y, y, Indeterminate},
        // c == a != b
        {z, x, z, Indeterminate},
        // CCW
        {x, y, z, CounterClockwise},
        // CW
        {z, y, x, Clockwise},

        // Edge cases:
        // The following points happen to be *exactly collinear* along a line that it
        // approximate tangent to the surface of the unit sphere. In fact, C is the
        // exact midpoint of the line segment AB. All of these points are close
        // enough to unit length to satisfy S2::IsUnitLength().
        {
            // Until we get ExactSign, this will only return Indeterminate.
            // It should be Clockwise.
            poA, poB, poC, Indeterminate,
        },

        // The points "x1" and "x2" are exactly proportional, i.e. they both lie
        // on a common line through the origin. Both points are considered to be
        // normalized, and in fact they both satisfy (x == x.Normalize()).
        // Therefore the triangle (x1, x2, -x1) consists of three distinct points
        // that all lie on a common line through the origin.
        {
            // Until we get ExactSign, this will only return Indeterminate.
            // It should be CounterClockwise.
            x1, x2, Point{x1.Mul(-1.0)}, Indeterminate,
        },

        // Here are two more points that are distinct, exactly proportional, and
        // that satisfy (x == x.Normalize()).
        {
            // Until we get ExactSign, this will only return Indeterminate.
            // It should be Clockwise.
            x3, x4, Point{x3.Mul(-1.0)}, Indeterminate,
        },

        // The following points demonstrate that Normalize() is not idempotent,
        // i.e. y0.Normalize() != y0.Normalize().Normalize(). Both points satisfy
        // S2::IsNormalized(), though, and the two points are exactly proportional.
        {
            // Until we get ExactSign, this will only return Indeterminate.
            // It should be CounterClockwise.
            y1, y2, Point{y1.Mul(-1.0)}, Indeterminate,
        },
    }

    for _, test := range tests {
        result := RobustSign(test.p1, test.p2, test.p3)
        if result != test.want {
            t.Errorf("RobustSign(%v, %v, %v) got %v, want %v",
                test.p1, test.p2, test.p3, result, test.want)
        }
        // Test RobustSign(b,c,a) == RobustSign(a,b,c) for all a,b,c
        rotated := RobustSign(test.p2, test.p3, test.p1)
        if rotated != result {
            t.Errorf("RobustSign(%v, %v, %v) vs Rotated RobustSign(%v, %v, %v) got %v, want %v",
                test.p1, test.p2, test.p3, test.p2, test.p3, test.p1, rotated, result)
        }
        // Test RobustSign(c,b,a) == -RobustSign(a,b,c) for all a,b,c
        want := Clockwise
        if result == Clockwise {
            want = CounterClockwise
        } else if result == Indeterminate {
            want = Indeterminate
        }
        reversed := RobustSign(test.p3, test.p2, test.p1)
        if reversed != want {
            t.Errorf("RobustSign(%v, %v, %v) vs Reversed RobustSign(%v, %v, %v) got %v, want %v",
                test.p1, test.p2, test.p3, test.p3, test.p2, test.p1, reversed, -1*result)
        }
    }

    // Test cases that should not be indeterminate.
    /*
        Uncomment these tests once RobustSign is completed.
        if got := RobustSign(poA, poB, poC); got == Indeterminate {
            t.Errorf("RobustSign(%v,%v,%v) = %v, want not Indeterminate", poA, poA, poA, got)
        }
        if got := RobustSign(x1, x2, Point{x1.Mul(-1)}); got == Indeterminate {
            t.Errorf("RobustSign(%v,%v,%v) = %v, want not Indeterminate", x1, x2, x1.Mul(-1), got)
        }
        if got := RobustSign(x3, x4, Point{x3.Mul(-1)}); got == Indeterminate {
            t.Errorf("RobustSign(%v,%v,%v) = %v, want not Indeterminate", x3, x4, x3.Mul(-1), got)
        }
        if got := RobustSign(y1, y2, Point{y1.Mul(-1)}); got == Indeterminate {
            t.Errorf("RobustSign(%v,%v,%v) = %v, want not Indeterminate", x1, x2, y1.Mul(-1), got)
        }
    */
}

func TestPredicatesStableSignFailureRate(t *testing.T) {
    const earthRadiusKm = 6371.01
    const iters = 1000

    // Verify that stableSign is able to handle most cases where the three
    // points are as collinear as possible. (For reference, triageSign fails
    // almost 100% of the time on this test.)
    //
    // Note that the failure rate *decreases* as the points get closer together,
    // and the decrease is approximately linear. For example, the failure rate
    // is 0.4% for collinear points spaced 1km apart, but only 0.0004% for
    // collinear points spaced 1 meter apart.
    //
    //  1km spacing: <  1% (actual is closer to 0.4%)
    // 10km spacing: < 10% (actual is closer to 4%)
    want := 0.01
    spacing := 1.0

    // Estimate the probability that stableSign will not be able to compute
    // the determinant sign of a triangle A, B, C consisting of three points
    // that are as collinear as possible and spaced the given distance apart
    // by counting up the times it returns Indeterminate.
    failureCount := 0
    m := math.Tan(spacing / earthRadiusKm)
    for iter := 0; iter < iters; iter++ {
        f := randomFrame()
        a := f.col(0)
        x := f.col(1)

        b := Point{a.Sub(x.Mul(m)).Normalize()}
        c := Point{a.Add(x.Mul(m)).Normalize()}
        sign := stableSign(a, b, c)
        if sign != Indeterminate {
            // TODO(roberts): Once exactSign is implemented, uncomment this case.
            //if got := exactSign(a, b, c, true); got != sign {
            //	t.Errorf("exactSign(%v, %v, %v, true) = %v, want %v", a, b, c, got, sign)
            //}
        } else {
            failureCount++
        }
    }

    rate := float64(failureCount) / float64(iters)
    if rate >= want {
        t.Errorf("stableSign failure rate for spacing %v km = %v, want %v", spacing, rate, want)
    }
}

func BenchmarkSign(b *testing.B) {
    p1 := Point{r3.Vector{-3, -1, 4}}
    p2 := Point{r3.Vector{2, -1, -3}}
    p3 := Point{r3.Vector{1, -2, 0}}
    for i := 0; i < b.N; i++ {
        Sign(p1, p2, p3)
    }
}

// BenchmarkRobustSignSimple runs the benchmark for points that satisfy the first
// checks in RobustSign to compare the performance to that of Sign().
func BenchmarkRobustSignSimple(b *testing.B) {
    p1 := Point{r3.Vector{-3, -1, 4}}
    p2 := Point{r3.Vector{2, -1, -3}}
    p3 := Point{r3.Vector{1, -2, 0}}
    for i := 0; i < b.N; i++ {
        RobustSign(p1, p2, p3)
    }
}

// BenchmarkRobustSignNearCollinear runs the benchmark for points that are almost but not
// quite collinear, so the tests have to use most of the calculations of RobustSign
// before getting to an answer.
func BenchmarkRobustSignNearCollinear(b *testing.B) {
    for i := 0; i < b.N; i++ {
        RobustSign(poA, poB, poC)
    }
}
*/
