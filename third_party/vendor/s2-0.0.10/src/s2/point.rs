use std;

use cgmath::{Matrix, Matrix3, Vector3};

use crate::consts::*;
use crate::r3::vector::Vector;
use crate::s1;
use crate::s1::ChordAngle;
use crate::s1::*;
use crate::s2::cap::Cap;
use crate::s2::cell::Cell;
use crate::s2::latlng::LatLng;
use crate::s2::predicates::*;
use crate::s2::rect::Rect;
use crate::s2::region::Region;
use std::f64::consts::PI;

/// Point represents a point on the unit sphere as a normalized 3D vector.
/// Fields should be treated as read-only. Use one of the factory methods for creation.
#[derive(Clone, Copy, PartialEq, Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Point(pub Vector);

impl std::ops::Add<Point> for Point {
    type Output = Point;
    fn add(self, other: Point) -> Self::Output {
        &self + &other
    }
}
impl<'a, 'b> std::ops::Add<&'b Point> for &'a Point {
    type Output = Point;
    fn add(self, other: &'b Point) -> Self::Output {
        Point(&self.0 + &other.0)
    }
}

impl std::ops::Sub<Point> for Point {
    type Output = Point;
    fn sub(self, other: Point) -> Self::Output {
        &self - &other
    }
}
impl<'a, 'b> std::ops::Sub<&'b Point> for &'a Point {
    type Output = Point;
    fn sub(self, other: &'b Point) -> Self::Output {
        Point(&self.0 - &other.0)
    }
}

impl std::ops::Mul<Point> for Point {
    type Output = Point;
    fn mul(self, other: Point) -> Self::Output {
        &self * &other
    }
}
impl<'a, 'b> std::ops::Mul<&'b Point> for &'a Point {
    type Output = Point;
    fn mul(self, other: &'b Point) -> Self::Output {
        Point(&self.0 * &other.0)
    }
}

impl std::ops::Mul<f64> for Point {
    type Output = Point;
    fn mul(self, m: f64) -> Self::Output {
        Point(self.0 * m)
    }
}
impl<'a> std::ops::Mul<f64> for &'a Point {
    type Output = Point;
    fn mul(self, m: f64) -> Self::Output {
        Point(&self.0 * m)
    }
}

impl From<Point> for Vector3<f64> {
    fn from(p: Point) -> Self {
        (&p).into()
    }
}
impl<'a> From<&'a Point> for Vector3<f64> {
    fn from(p: &'a Point) -> Self {
        Vector3::new(p.0.x, p.0.y, p.0.z)
    }
}
impl From<Vector3<f64>> for Point {
    fn from(p: Vector3<f64>) -> Self {
        (&p).into()
    }
}
impl<'a> From<&'a Vector3<f64>> for Point {
    fn from(p: &'a Vector3<f64>) -> Self {
        Point(Vector::new(p.x, p.y, p.z))
    }
}

pub const ORIGIN: Point = Point(Vector {
    x: -0.0099994664350250197,
    y: 0.0025924542609324121,
    z: 0.99994664350250195,
});

impl Point {
    /// form_coords creates a new normalized point from coordinates.
    ///
    /// This always returns a valid point. If the given coordinates can not be normalized
    /// the origin point will be returned.
    ///
    /// This behavior is different from the C++ construction of a S2Point from coordinates
    /// (i.e. S2Point(x, y, z)) in that in C++ they do not Normalize.
    pub fn from_coords(x: f64, y: f64, z: f64) -> Self {
        if x == 0. && y == 0. && z == 0. {
            Point::origin()
        } else {
            Point(Vector { x, y, z }.normalize())
        }
    }

    /// origin returns a unique "origin" on the sphere for operations that need a fixed
    /// reference point. In particular, this is the "point at infinity" used for
    /// point-in-polygon testing (by counting the number of edge crossings).
    ///
    /// It should *not* be a point that is commonly used in edge tests in order
    /// to avoid triggering code to handle degenerate cases (this rules out the
    /// north and south poles). It should also not be on the boundary of any
    /// low-level S2Cell for the same reason.
    pub fn origin() -> Self {
        ORIGIN
    }

    /// cross returns a Point that is orthogonal to both p and op. This is similar to
    /// p.Cross(op) (the true cross product) except that it does a better job of
    /// ensuring orthogonality when the Point is nearly parallel to op, it returns
    /// a non-zero result even when p == op or p == -op and the result is a Point.
    ///
    /// It satisfies the following properties (f == cross):
    ///
    /// ```text
    /// (1) f(p, op) != 0 for all p, op
    /// (2) f(op,p) == -f(p,op) unless p == op or p == -op
    /// (3) f(-p,op) == -f(p,op) unless p == op or p == -op
    /// (4) f(p,-op) == -f(p,op) unless p == op or p == -op
    /// ```
    pub fn cross(&self, other: &Self) -> Self {
        // NOTE(dnadasi): In the C++ API the equivalent method here was known as "RobustCrossProd",
        // but point_cross more accurately describes how this method is used.
        let v = (self.0 + other.0).cross(&(other.0 - self.0));

        // Compare exactly to the 0 vector.
        if v.x == 0. && v.y == 0. && v.z == 0. {
            // The only result that makes sense mathematically is to return zero, but
            // we find it more convenient to return an arbitrary orthogonal vector.
            Point(self.0.ortho())
        } else {
            Point(v)
        }
    }

    /// distance returns the angle between two points.
    pub fn distance(&self, b: &Point) -> s1::Angle {
        self.0.angle(&b.0)
    }

    /// approx_eq reports whether the two points are similar enough to be equal.
    pub fn approx_eq(&self, other: &Self) -> bool {
        self.0.angle(&other.0).rad() <= EPSILON
    }

    /// norm returns the point's norm.
    pub fn norm(&self) -> f64 {
        self.0.norm()
    }

    pub fn normalize(&self) -> Self {
        Point(self.0.normalize())
    }

    pub fn ortho(&self) -> Self {
        Point(self.0.ortho())
    }

    // frame returns the orthonormal frame for the given point on the unit sphere.
    //struct for Frame and From<>/Into<>?
    //TODO: private
    pub fn frame(&self) -> Matrix3<f64> {
        let c2 = *self;
        let c1 = self.ortho();
        let c0 = Point(c1.0.cross(&self.0));

        Matrix3::from_cols(c0.into(), c1.into(), c2.into())
    }
}

// from_frame returns the coordinates of the given point in standard axis-aligned basis
// from its orthonormal basis m.
// The resulting point p satisfies the identity (p == m * q).
//TODO: private
pub fn from_frame(m: &Matrix3<f64>, p: &Point) -> Point {
    let v: Vector3<f64> = p.into();
    (m * v).into()
}

// to_frame returns the coordinates of the given point with respect to its orthonormal basis m.
// The resulting point q satisfies the identity (m * q == p).
//TODO: private
pub fn to_frame(m: &Matrix3<f64>, p: &Point) -> Point {
    // The inverse of an orthonormal matrix is its transpose.
    Point::from(m.transpose() * Vector3::from(p))
}

/// ordered_ccw returns true if the edges OA, OB, and OC are encountered in that
/// order while sweeping CCW around the point O.
///
/// You can think of this as testing whether A <= B <= C with respect to the
/// CCW ordering around O that starts at A, or equivalently, whether B is
/// contained in the range of angles (inclusive) that starts at A and extends
/// CCW to C. Properties:
///
///  (1) If OrderedCCW(a,b,c,o) && OrderedCCW(b,a,c,o), then a == b
///  (2) If OrderedCCW(a,b,c,o) && OrderedCCW(a,c,b,o), then b == c
///  (3) If OrderedCCW(a,b,c,o) && OrderedCCW(c,b,a,o), then a == b == c
///  (4) If a == b or b == c, then OrderedCCW(a,b,c,o) is true
///  (5) Otherwise if a == c, then OrderedCCW(a,b,c,o) is false
pub fn ordered_ccw(a: &Point, b: &Point, c: &Point, o: &Point) -> bool {
    let mut sum = 0;
    if robust_sign(b, o, a) != Direction::Clockwise {
        sum += 1;
    }
    if robust_sign(c, o, b) != Direction::Clockwise {
        sum += 1;
    }
    if robust_sign(a, o, c) == Direction::CounterClockwise {
        sum += 1;
    }
    sum >= 2
}

/// point_area returns the area on the unit sphere for the triangle defined by the
/// given points.
///
/// This method is based on l'Huilier's theorem,
///
///   tan(E/4) = sqrt(tan(s/2) tan((s-a)/2) tan((s-b)/2) tan((s-c)/2))
///
/// where E is the spherical excess of the triangle (i.e. its area),
///       a, b, c are the side lengths, and
///       s is the semiperimeter (a + b + c) / 2.
///
/// The only significant source of error using l'Huilier's method is the
/// cancellation error of the terms (s-a), (s-b), (s-c). This leads to a
/// *relative* error of about 1e-16 * s / min(s-a, s-b, s-c). This compares
/// to a relative error of about 1e-15 / E using Girard's formula, where E is
/// the true area of the triangle. Girard's formula can be even worse than
/// this for very small triangles, e.g. a triangle with a true area of 1e-30
/// might evaluate to 1e-5.
///
/// So, we prefer l'Huilier's formula unless dmin < s * (0.1 * E), where
/// dmin = min(s-a, s-b, s-c). This basically includes all triangles
/// except for extremely long and skinny ones.
///
/// Since we don't know E, we would like a conservative upper bound on
/// the triangle area in terms of s and dmin. It's possible to show that
/// E <= k1 * s * sqrt(s * dmin), where k1 = 2*sqrt(3)/Pi (about 1).
/// Using this, it's easy to show that we should always use l'Huilier's
/// method if dmin >= k2 * s^5, where k2 is about 1e-2. Furthermore,
/// if dmin < k2 * s^5, the triangle area is at most k3 * s^4, where
/// k3 is about 0.1. Since the best case error using Girard's formula
/// is about 1e-15, this means that we shouldn't even consider it unless
/// s >= 3e-4 or so.
pub fn point_area(a: &Point, b: &Point, c: &Point) -> f64 {
    let sa = b.0.angle(&c.0).rad();
    let sb = c.0.angle(&a.0).rad();
    let sc = a.0.angle(&b.0).rad();
    let s = 0.5 * (sa + sb + sc);
    if s >= 3e-4 {
        // Consider whether Girard's formula might be more accurate.
        let dmin = s - sa.max(sb.max(sc));
        if dmin < 1e-2 * s * s * s * s * s {
            // This triangle is skinny enough to use Girard's formula.
            let ab = a.cross(b).0;
            let bc = b.cross(c).0;
            let ac = a.cross(c).0;

            let ab_ac = ab.angle(&ac).rad();
            let ab_bc = ab.angle(&bc).rad();
            let bc_ac = bc.angle(&ac).rad();
            let area = (ab_ac - ab_bc + bc_ac).max(0.0);

            if dmin < s * 0.1 * area {
                return area;
            }
        }
    }

    // Use l'Huilier's formula.
    4. * ((0.5 * s).tan()
        * (0.5 * (s - sa)).tan()
        * (0.5 * (s - sb)).tan()
        * (0.5 * (s - sc)).tan())
    .max(0.)
    .sqrt()
    .atan()
}

/// true_centroid returns the true centroid of the spherical triangle ABC multiplied by the
/// signed area of spherical triangle ABC. The result is not normalized.
/// The reasons for multiplying by the signed area are (1) this is the quantity
/// that needs to be summed to compute the centroid of a union or difference of triangles,
/// and (2) it's actually easier to calculate this way. All points must have unit length.
///
/// The true centroid (mass centroid) is defined as the surface integral
/// over the spherical triangle of (x,y,z) divided by the triangle area.
/// This is the point that the triangle would rotate around if it was
/// spinning in empty space.
///
/// The best centroid for most purposes is the true centroid. Unlike the
/// planar and surface centroids, the true centroid behaves linearly as
/// regions are added or subtracted. That is, if you split a triangle into
/// pieces and compute the average of their centroids (weighted by triangle
/// area), the result equals the centroid of the original triangle. This is
/// not true of the other centroids.
pub fn true_centroid(a: &Point, b: &Point, c: &Point) -> Point {
    let sa = b.distance(&c).rad();
    let ra = if sa == 0. { 1. } else { sa / sa.sin() };
    let sb = c.distance(a).rad();
    let rb = if sb == 0. { 1. } else { sb / sb.sin() };
    let sc = a.distance(&b).rad();
    let rc = if sc == 0. { 1. } else { sc / sc.sin() };

    // Now compute a point M such that:
    //
    //  [Ax Ay Az] [Mx]                       [ra]
    //  [Bx By Bz] [My]  = 0.5 * det(A,B,C) * [rb]
    //  [Cx Cy Cz] [Mz]                       [rc]
    //
    // To improve the numerical stability we subtract the first row (A) from the
    // other two rows; this reduces the cancellation error when A, B, and C are
    // very close together. Then we solve it using Cramer's rule.
    //
    // This code still isn't as numerically stable as it could be.
    // The biggest potential improvement is to compute B-A and C-A more
    // accurately so that (B-A)x(C-A) is always inside triangle ABC.
    let x = Vector::new(a.0.x, b.0.x - a.0.x, c.0.x - a.0.x);
    let y = Vector::new(a.0.y, b.0.y - a.0.y, c.0.y - a.0.y);
    let z = Vector::new(a.0.z, b.0.z - a.0.z, c.0.z - a.0.z);
    let r = Vector::new(ra, rb - ra, rc - ra);

    Point(Vector::new(
        y.cross(&z).dot(&r),
        z.cross(&x).dot(&r),
        x.cross(&y).dot(&r),
    )) * 0.5
}

/// planar_centroid returns the centroid of the planar triangle ABC, which is not normalized.
/// It can be normalized to unit length to obtain the "surface centroid" of the corresponding
/// spherical triangle, i.e. the intersection of the three medians. However,
/// note that for large spherical triangles the surface centroid may be
/// nowhere near the intuitive "center" (see example in TrueCentroid comments).
///
/// Note that the surface centroid may be nowhere near the intuitive
/// "center" of a spherical triangle. For example, consider the triangle
/// with vertices A=(1,eps,0), B=(0,0,1), C=(-1,eps,0) (a quarter-sphere).
/// The surface centroid of this triangle is at S=(0, 2*eps, 1), which is
/// within a distance of 2*eps of the vertex B. Note that the median from A
/// (the segment connecting A to the midpoint of BC) passes through S, since
/// this is the shortest path connecting the two endpoints. On the other
/// hand, the true centroid is at M=(0, 0.5, 0.5), which when projected onto
/// the surface is a much more reasonable interpretation of the "center" of
/// this triangle.
pub fn planar_centroid(a: &Point, b: &Point, c: &Point) -> Point {
    Point((&(a.0 + b.0) + &c.0) * (1. / 3.))
}

impl Point {
    /// chordangle constructs a ChordAngle corresponding to the distance
    /// between the two given points. The points must be unit length.
    pub fn chordangle(&self, other: &Point) -> ChordAngle {
        ChordAngle(4f64.min((self.0 - other.0).norm2()))
    }
}

/// regular_points generates a slice of points shaped as a regular polygon with
/// the numVertices vertices, all located on a circle of the specified angular radius
/// around the center. The radius is the actual distance from center to each vertex.
/// TODO: private?
pub fn regular_points(center: &Point, radius: Angle, num_vertices: usize) -> Vec<Point> {
    regular_points_for_frame(&center.frame(), radius, num_vertices)
}

/// regular_points_for_frame generates a slice of points shaped as a regular polygon
/// with numVertices vertices, all on a circle of the specified angular radius around
/// the center. The radius is the actual distance from the center to each vertex.
/// TODO: private?
fn regular_points_for_frame(
    frame: &Matrix3<f64>,
    radius: Angle,
    num_vertices: usize,
) -> Vec<Point> {
    // We construct the loop in the given frame coordinates, with the center at
    // (0, 0, 1). For a loop of radius r, the loop vertices have the form
    // (x, y, z) where x^2 + y^2 = sin(r) and z = cos(r). The distance on the
    // sphere (arc length) from each vertex to the center is acos(cos(r)) = r.
    let z = radius.rad().cos();
    let r = radius.rad().sin();
    let radian_step = 2. * PI / (num_vertices as f64);

    let mut vertices = Vec::with_capacity(num_vertices);

    for i in 0..num_vertices {
        let angle = (i as f64) * radian_step;
        let p = Point(Vector::new(r * angle.cos(), r * angle.sin(), z));
        vertices.push(from_frame(frame, &p).normalize());
    }

    vertices
}

impl Region for Point {
    /// cap_bound returns a bounding cap for this point.
    fn cap_bound(&self) -> Cap {
        Cap::from(self)
    }

    /// rect_bound returns a bounding latitude-longitude rectangle from this point.
    fn rect_bound(&self) -> Rect {
        Rect::from(LatLng::from(self))
    }

    /// contains_cell returns false as Points do not contain any other S2 types.
    fn contains_cell(&self, _: &Cell) -> bool {
        false
    }

    /// intersects_cell reports whether this Point intersects the given cell.
    fn intersects_cell(&self, c: &Cell) -> bool {
        c.contains_point(self)
    }
}

impl Point {
    pub fn contains(&self, other: &Point) -> bool {
        self == other
    }
}

// TODO: Differences from C++
// Rotate
// Angle
// TurnAngle
// SignedArea

#[cfg(test)]
#[allow(non_upper_case_globals)]
mod tests {
    use super::*;

    use crate::s2::stuv::st_to_uv;
    use std::f64::consts::PI;

    #[test]
    fn test_origin_point() {
        assert!((Point::origin().norm() - 1.).abs() <= EPSILON);

        // The point chosen below is about 66km from the north pole towards the East
        // Siberian Sea. The purpose of the stToUV(2/3) calculation is to keep the
        // origin as far away as possible from the longitudinal edges of large
        // Cells. (The line of longitude through the chosen point is always 1/3
        // or 2/3 of the way across any Cell with longitudinal edges that it
        // passes through.)
        let p = Point::from_coords(-0.01, 0.01 * st_to_uv(2. / 3.), 1.);
        assert!(p.approx_eq(&Point::origin()));

        // Check that the origin is not too close to either pole.
        // The Earth's mean radius in kilometers (according to NASA).
        const EARTH_RADIUS_KM: f64 = 6371.01;
        assert!(Point::origin().0.z.acos() * EARTH_RADIUS_KM > 50.);
    }

    fn test_point_cross_case(expected: f64, v1: Vector, v2: Vector) {
        let p1 = Point(v1);
        let p2 = Point(v2);

        let result = p1.cross(&p2);
        assert_f64_eq!(expected, result.norm());
        assert_f64_eq!(0., result.0.dot(&p1.0));
        assert_f64_eq!(0., result.0.dot(&p2.0));
    }

    #[test]
    fn test_point_cross() {
        test_point_cross_case(1., Vector::new(1., 0., 0.), Vector::new(1., 0., 0.));
        test_point_cross_case(2., Vector::new(1., 0., 0.), Vector::new(0., 1., 0.));
        test_point_cross_case(2., Vector::new(0., 1., 0.), Vector::new(1., 0., 0.));
        test_point_cross_case(
            2. * 934f64.sqrt(),
            Vector::new(1., 2., 3.),
            Vector::new(-4., 5., -6.),
        );
    }

    fn test_point_distance_case(expected: f64, v1: Vector, v2: Vector) {
        let p1 = Point(v1);
        let p2 = Point(v2);

        assert_f64_eq!(expected, p1.distance(&p2).rad());
        assert_f64_eq!(expected, p2.distance(&p1).rad());
    }

    #[test]
    fn test_point_distance() {
        test_point_distance_case(0., Vector::new(1., 0., 0.), Vector::new(1., 0., 0.));
        test_point_distance_case(PI / 2., Vector::new(1., 0., 0.), Vector::new(0., 1., 0.));
        test_point_distance_case(PI / 2., Vector::new(1., 0., 0.), Vector::new(0., 1., 1.));
        test_point_distance_case(
            1.2055891055045298,
            Vector::new(1., 2., 3.),
            Vector::new(2., 3., -1.),
        );
    }

    use crate::s1::Angle;
    use crate::s2::random;

    #[test]
    fn test_chordangle_between_points() {
        let mut rng = random::rng();
        for _ in 0..10 {
            let m = random::frame(&mut rng);

            let x: Point = m.x.into();
            let y: Point = m.y.into();
            let z: Point = m.z.into();

            assert_eq!(0., Angle::from(z.chordangle(&z)).rad());
            assert!(
                f64_near(PI, Angle::from((&z * -1.).chordangle(&z)).rad(), 1e-7),
                "{} != {}",
                PI,
                Angle::from((&z * -1.).chordangle(&z)).rad()
            );
            assert_f64_eq!(PI / 2., Angle::from(x.chordangle(&z)).rad());

            let w = (&y + &z).normalize();
            assert_f64_eq!(PI / 4., Angle::from(w.chordangle(&z)).rad());
        }
    }

    fn approx_eq_case(want: bool, p1: Point, p2: Point) {
        assert_eq!(want, p1.approx_eq(&p2));
    }

    #[test]
    fn test_point_approx_eq() {
        approx_eq_case(
            true,
            Point::from_coords(1., 0., 0.),
            Point::from_coords(1., 0., 0.),
        );
        approx_eq_case(
            false,
            Point::from_coords(1., 0., 0.),
            Point::from_coords(0., 1., 0.),
        );
        approx_eq_case(
            false,
            Point::from_coords(1., 0., 0.),
            Point::from_coords(0., 1., 1.),
        );
        approx_eq_case(
            false,
            Point::from_coords(1., 0., 0.),
            Point::from_coords(-1., 0., 0.),
        );
        approx_eq_case(
            false,
            Point::from_coords(1., 2., 3.),
            Point::from_coords(2., 3., -1.),
        );
        approx_eq_case(
            true,
            Point::from_coords(1., 0., 0.),
            Point::from_coords(1. * (1. + EPSILON), 0., 0.),
        );
        approx_eq_case(
            true,
            Point::from_coords(1., 0., 0.),
            Point::from_coords(1. * (1. - EPSILON), 0., 0.),
        );
        approx_eq_case(
            true,
            Point::from_coords(1., 0., 0.),
            Point::from_coords(1. + EPSILON, 0., 0.),
        );
        approx_eq_case(
            true,
            Point::from_coords(1., 0., 0.),
            Point::from_coords(1. - EPSILON, 0., 0.),
        );
        approx_eq_case(
            true,
            Point::from_coords(1., 0., 0.),
            Point::from_coords(1., EPSILON, 0.),
        );
        approx_eq_case(
            false,
            Point::from_coords(1., 0., 0.),
            Point::from_coords(1., EPSILON, EPSILON),
        );
        approx_eq_case(
            false,
            Point::from_coords(1., EPSILON, 0.),
            Point::from_coords(1., -EPSILON, EPSILON),
        );
    }

    const pz: Point = Point(Vector {
        x: 0.,
        y: 0.,
        z: 1.,
    });
    const p000: Point = Point(Vector {
        x: 1.,
        y: 0.,
        z: 0.,
    });
    const p045: Point = Point(Vector {
        x: 1.,
        y: 1.,
        z: 0.,
    });
    const p090: Point = Point(Vector {
        x: 0.,
        y: 1.,
        z: 0.,
    });
    const p180: Point = Point(Vector {
        x: -1.,
        y: 0.,
        z: 0.,
    });
    // Degenerate triangles.
    const pr: Point = Point(Vector {
        x: 0.257,
        y: -0.5723,
        z: 0.112,
    });
    const pq: Point = Point(Vector {
        x: -0.747,
        y: 0.401,
        z: 0.2235,
    });
    const g1: Point = Point(Vector {
        x: 1.,
        y: 1.,
        z: 1.,
    });
    lazy_static! {
        // For testing the Girard area fall through case.
        static ref g2: Point = (g1 + (pr * 1e-15)).normalize();
        static ref g3: Point = (g1 + (pq * 1e-15)).normalize();
    }

    fn point_area_case(a: &Point, b: &Point, c: &Point, want: f64, nearness: f64) {
        assert!(f64_near(want, point_area(&a, &b, &c), nearness));
    }

    #[test]
    fn test_point_area() {
        const EPSILON: f64 = 1e-10;
        point_area_case(&p000, &p090, &pz, PI / 2., 0.);
        // This test case should give 0 as the EPSILON, but either Go or C++'s value for Pi,
        // or the accuracy of the multiplications along the way, cause a difference ~15 decimal
        // places into the result, so it is not quite a difference of 0.
        point_area_case(&p045, &pz, &p180, 3.0 * PI / 4.0, 1e-14);
        // Make sure that Area has good *relative* accuracy even for very small areas.
        point_area_case(
            &Point(Vector::new(EPSILON, 0., 1.)),
            &Point(Vector::new(0., EPSILON, 1.)),
            &pz,
            0.5 * EPSILON * EPSILON,
            1e-14,
        );
        // Make sure that it can handle degenerate triangles.
        point_area_case(&pr, &pr, &pr, 0., 0.);
        point_area_case(&pr, &pq, &pr, 0., 1e-15);
        point_area_case(&p000, &p045, &p090, 0., 0.);
        // Try a very long and skinny triangle.
        point_area_case(
            &p000,
            &Point(Vector::new(1., 1., EPSILON)),
            &p090,
            5.8578643762690495119753e-11,
            1e-9,
        );
        // TODO(roberts):
        // C++ includes a 10,000 loop of perterbations to test out the Girard area
        // computation is less than some noise threshold.
        // Do we need that many? Will one or two suffice?
        point_area_case(&g1, &g2, &g3, 0.0, 1e-15);
    }

    fn area_quater_hemi_case(a: &Point, b: &Point, c: &Point, d: &Point, e: &Point, want: f64) {
        let area =
            point_area(a, b, c) + point_area(a, c, d) + point_area(a, d, e) + point_area(a, e, b);
        assert_f64_eq!(want, area);
    }

    #[test]
    fn test_point_area_quater_hemisphere() {
        // Triangles with near-180 degree edges that sum to a quarter-sphere.
        area_quater_hemi_case(
            &Point(Vector::new(1., 0.1 * EPSILON, EPSILON)),
            &p000,
            &p045,
            &p180,
            &pz,
            PI,
        );
        // Four other triangles that sum to a quarter-sphere.
        area_quater_hemi_case(
            &Point(Vector::new(1., 1., EPSILON)),
            &p000,
            &p045,
            &p180,
            &pz,
            PI,
        );
        // TODO(roberts):
        // C++ Includes a loop of 100 perturbations on a hemisphere for more tests.
    }

    fn planar_centroid_case(p0: &Point, p1: &Point, p2: &Point, want: &Point) {
        assert_eq!(*want, planar_centroid(p0, p1, p2));
    }

    #[test]
    fn test_point_planar_centroid() {
        // xyz axis
        planar_centroid_case(
            &Point(Vector::new(0., 0., 1.)),
            &Point(Vector::new(0., 1., 0.)),
            &Point(Vector::new(1., 0., 0.)),
            &Point(Vector::new(1. / 3., 1. / 3., 1. / 3.)),
        );

        // same point
        planar_centroid_case(
            &Point(Vector::new(1., 0., 0.)),
            &Point(Vector::new(1., 0., 0.)),
            &Point(Vector::new(1., 0., 0.)),
            &Point(Vector::new(1., 0., 0.)),
        );
    }

    use rand::Rng;

    #[test]
    fn test_point_true_centroid() {
        let mut rng = random::rng();

        // Test TrueCentroid with very small triangles. This test assumes that
        // the triangle is small enough so that it is nearly planar.
        // The centroid of a planar triangle is at the intersection of its
        // medians, which is two-thirds of the way along each median.
        for _ in 0..100 {
            let f = random::frame(&mut rng);
            let p = Point::from(f.x);
            let x = Point::from(f.y);
            let y = Point::from(f.z);
            let d = 1e-4 * 1e-4f64.powf(rng.gen_range(0., 1.));

            // Make a triangle with two equal sides.
            {
                let p0 = (p - (x * d)).normalize();
                let p1 = (p + (x * d)).normalize();
                let p2 = (p + (y * (d * 3.))).normalize();
                let want = (p + (y * d)).normalize();

                let got = true_centroid(&p0, &p1, &p2).normalize();
                assert!(got.distance(&want).rad() < 2e-8);
            }

            {
                let p0 = p;
                let p1 = (p + (x * (d * 3.))).normalize();
                let p2 = (p + (y * (d * 6.))).normalize();
                let want = (p + ((x + (y * 2.)) * d)).normalize();

                let got = true_centroid(&p0, &p1, &p2).normalize();
                assert!(got.distance(&want).rad() < 2e-8);
            }
        }
    }

    #[test]
    fn test_point_regular_points() {
        // Conversion to/from degrees has a little more variability than the default EPSILON.
        const EPSILON: f64 = 1e-13;
        let center = Point::from(LatLng::new(Deg(80.).into(), Deg(135.).into()));
        let radius = Angle::from(Deg(20.));
        let pts = regular_points(&center, radius, 4);
        assert_eq!(4, pts.len());

        let lls = pts.iter().map(|p| LatLng::from(p)).collect::<Vec<_>>();
        let cll = LatLng::from(&center);

        // Make sure that the radius is correct.
        let want_dist = 20.;
        for ll in lls.iter() {
            let got = cll.distance(ll).deg();
            assert!(f64_near(want_dist, got, EPSILON));
        }

        let want_angle = PI / 2.;
        // Make sure the angle between each point is correct.
        for i in 0..4 {
            let v0 = pts[(4 + i + 1) % 4];
            let v1 = pts[(4 + i) % 4];
            let v2 = pts[(4 + i - 1) % 4];
            assert!(f64_near(
                want_angle,
                ((v0 - v1).0.angle(&(v2 - v1).0)).rad(),
                EPSILON
            ));
        }

        // Make sure that all edges of the polygon have the same length.
        let want_len = 27.990890717782829;
        for i in 0..4 {
            let ll1 = &lls[i];
            let ll2 = &lls[(i + 1) % 4];
            assert!(f64_near(want_len, ll1.distance(ll2).deg(), EPSILON));
        }

        // Spot check an actual coordinate now that we know the points are spaced
        // evenly apart at the same angles and radii.
        assert!(f64_near(lls[0].lat.deg(), 62.162880741097204, EPSILON));
        assert!(f64_near(lls[0].lng.deg(), 103.11051028343407, EPSILON));
    }

    #[test]
    fn test_point_region() {
        let p = Point(Vector::new(1., 0., 0.));
        let r = Point(Vector::new(1., 0., 0.));

        assert!(r.contains(&p));
        assert!(p.contains(&r));
        assert_eq!(false, r.contains(&Point(Vector::new(1., 0., 1.))));

        assert!(r.cap_bound().approx_eq(&Cap::from(&r)));
        assert!(r.rect_bound().approx_eq(&Rect::from(LatLng::from(&p))));

        let cell = Cell::from(&p);
        assert_eq!(false, r.contains_cell(&cell));
        assert_eq!(true, r.intersects_cell(&cell));
    }

    /*
    func BenchmarkPointArea(b *testing.B) {
        for i := 0; i < b.N; i++ {
            PointArea(p000, p090, pz)
        }
    }

    func BenchmarkPointAreaGirardCase(b *testing.B) {
        for i := 0; i < b.N; i++ {
            PointArea(g1, g2, g3)
        }
    }
    */

    use cgmath::SquareMatrix;

    // tests for frame
    #[test]
    fn test_point_frames() {
        let z = Point::from_coords(0.2, 0.5, -3.3);
        let m = z.frame();

        assert!(Point::from(m.x).0.is_unit());
        assert!(Point::from(m.y).0.is_unit());
        assert_f64_eq!(m.determinant(), 1.);

        assert!(Point(Vector::new(1., 0., 0.)).approx_eq(&to_frame(&m, &Point::from(m.x))));
        assert!(Point(Vector::new(0., 1., 0.)).approx_eq(&to_frame(&m, &Point::from(m.y))));
        assert!(Point(Vector::new(0., 0., 1.)).approx_eq(&to_frame(&m, &Point::from(m.z))));

        assert!(from_frame(&m, &Point(Vector::new(1., 0., 0.))).approx_eq(&Point::from(m.x)));
        assert!(from_frame(&m, &Point(Vector::new(0., 1., 0.))).approx_eq(&Point::from(m.y)));
        assert!(from_frame(&m, &Point(Vector::new(0., 0., 1.))).approx_eq(&Point::from(m.z)));
    }
}
