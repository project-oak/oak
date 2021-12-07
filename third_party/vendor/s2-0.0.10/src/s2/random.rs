use cgmath;
use std::f64::consts::PI;

use crate::s2::cap::Cap;
use crate::s2::cellid::*;
use crate::s2::point::{self, Point};
use rand;
use rand::Rng;

pub fn rng() -> rand::prng::XorShiftRng {
    use rand::prelude::*;

    rand::prng::XorShiftRng::from_rng(rand::thread_rng()).expect("failed to get rng")
}

/// skewed_int returns a number in the range [0,2^max_log-1] with bias towards smaller numbers.
pub fn skewed_int<R>(rng: &mut R, max_log: usize) -> usize
where
    R: Rng,
{
    let base = rng.gen_range(0, max_log + 1);
    rng.gen_range(0, 1 << 31) & ((1 << base) - 1)
}

/// cap returns a cap with a random axis such that the log of its area is
/// uniformly distributed between the logs of the two given values. The log of
/// the cap angle is also approximately uniformly distributed.
pub fn cap<R>(rng: &mut R, min_area: f64, max_area: f64) -> Cap
where
    R: Rng,
{
    let cap_area = max_area * (min_area / max_area).powf(rng.gen_range(0., 1.));
    Cap::from_center_area(&point(rng), cap_area)
}

/// point returns a random unit-length vector.
pub fn point<R: Rng>(rng: &mut R) -> Point {
    Point::from_coords(
        rng.gen_range(-1., 1.),
        rng.gen_range(-1., 1.),
        rng.gen_range(-1., 1.),
    )
}

pub fn frame<R: Rng>(rng: &mut R) -> cgmath::Matrix3<f64> {
    let z = point(rng);
    frame_at_point(rng, z)
}

pub fn frame_at_point<R: Rng>(rng: &mut R, z: Point) -> cgmath::Matrix3<f64> {
    let p = point(rng);
    let x = z.cross(&p).normalize();
    let y = z.cross(&x).normalize();

    cgmath::Matrix3::from_cols(x.into(), y.into(), z.into())
}

pub fn cellid<R>(rng: &mut R) -> CellID
where
    R: Rng,
{
    let level = rng.gen_range(0, MAX_LEVEL + 1);
    cellid_for_level(rng, level)
}

pub fn cellid_for_level<R>(rng: &mut R, level: u64) -> CellID
where
    R: Rng,
{
    let face = rng.gen_range(0, NUM_FACES as u64);
    let pos = rng.next_u64() & ((1 << POS_BITS) - 1);
    let cellid = CellID::from_face_pos_level(face, pos, level);
    assert_eq!(face, cellid.face() as u64);
    assert_eq!(level, cellid.level());

    cellid
}

pub fn one_in<R>(rng: &mut R, n: u64) -> bool
where
    R: Rng,
{
    rng.gen_range(0, n) == 0
}

// sample_point_from_cap returns a point chosen uniformly at random (with respect
// to area) from the given cap.
pub fn sample_point_from_cap<R>(rng: &mut R, c: Cap) -> Point
where
    R: Rng,
{
    // We consider the cap axis to be the "z" axis. We choose two other axes to
    // complete the coordinate frame.
    let center = c.center();
    let m = center.frame();

    // The surface area of a spherical cap is directly proportional to its
    // height. First we choose a random height, and then we choose a random
    // point along the circle at that height.
    let h = rng.gen_range(0., 1.) * c.height();
    let theta = 2. * PI * rng.gen_range(0., 1.);
    let r = (h * (2. - h)).sqrt();

    // The result should already be very close to unit-length, but we might as
    // well make it accurate as possible.
    point::from_frame(
        &m,
        &Point::from_coords(theta.cos() * r, theta.sin() * r, 1. - h).normalize(),
    )
}
