use crate::r3::vector::Vector;
use crate::s2::cellid::*;
use crate::s2::point::Point;

const MAX_SITI: u64 = MAX_SIZE << 1;

pub fn siti_to_st(si: u64) -> f64 {
    if si > MAX_SITI {
        1f64
    } else {
        (si as f64) / (MAX_SITI as f64)
    }
}

#[cfg(test)]
fn st_to_siti(s: f64) -> u64 {
    if s < 0. {
        (s * (MAX_SITI as f64) - 0.5) as u64
    } else {
        (s * (MAX_SITI as f64) + 0.5) as u64
    }
}

pub fn st_to_uv(s: f64) -> f64 {
    if s >= 0.5 {
        (1. / 3.) * (4. * s * s - 1.)
    } else {
        (1. / 3.) * (1. - 4. * (1. - s) * (1. - s))
    }
}

pub fn uv_to_st(u: f64) -> f64 {
    if u >= 0. {
        0.5 * (1. + 3. * u).sqrt()
    } else {
        1. - 0.5 * (1. - 3. * u).sqrt()
    }
}

pub fn face(r: &Vector) -> u8 {
    let abs = r.abs();
    let mut id = 0;
    let mut value = r.x;
    if abs.y > abs.x {
        id = 1;
        value = r.y;
    }
    if abs.z > value.abs() {
        id = 2;
        value = r.z;
    }
    if value < 0. {
        id += 3;
    }
    id
}

pub fn valid_face_xyz_to_uv(face: u8, r: &Vector) -> (f64, f64) {
    match face {
        0 => (r.y / r.x, r.z / r.x),
        1 => (-r.x / r.y, r.z / r.y),
        2 => (-r.x / r.z, -r.y / r.z),
        3 => (r.z / r.x, r.y / r.x),
        4 => (r.z / r.y, -r.x / r.y),
        5 => (-r.y / r.z, -r.x / r.z),
        _ => unimplemented!(),
    }
}

pub fn xyz_to_face_uv(r: &Vector) -> (u8, f64, f64) {
    let f = face(r);
    let (u, v) = valid_face_xyz_to_uv(f, r);
    (f, u, v)
}

pub fn face_uv_to_xyz(face: u8, u: f64, v: f64) -> Vector {
    match face {
        0 => Vector::new(1., u, v),
        1 => Vector::new(-u, 1., v),
        2 => Vector::new(-u, -v, 1.),
        3 => Vector::new(-1., -v, -u),
        4 => Vector::new(v, -1., -u),
        5 => Vector::new(v, u, -1.),
        _ => unimplemented!(),
    }
}

pub fn face_xyz_to_uv(face: u8, p: &Point) -> Option<(f64, f64)> {
    let invalid = match face {
        0 => p.0.x <= 0.,
        1 => p.0.y <= 0.,
        2 => p.0.z <= 0.,
        3 => p.0.x >= 0.,
        4 => p.0.y >= 0.,
        5 => p.0.z >= 0.,
        _ => unimplemented!(),
    };
    if invalid {
        None
    } else {
        Some(valid_face_xyz_to_uv(face, &p.0))
    }
}

#[cfg(test)]
fn face_xyz_to_uvw(face: u8, p: &Point) -> Point {
    let v = &p.0;
    match face {
        0 => Point(Vector::new(v.y, v.z, v.x)),
        1 => Point(Vector::new(-v.x, v.z, v.y)),
        2 => Point(Vector::new(-v.x, -v.y, v.z)),
        3 => Point(Vector::new(-v.z, -v.y, -v.x)),
        4 => Point(Vector::new(-v.z, v.x, -v.y)),
        5 => Point(Vector::new(v.y, v.x, -v.z)),
        _ => unimplemented!(),
    }
}

#[cfg(test)]
fn face_siti_to_xyz(face: u8, si: u64, ti: u64) -> Point {
    Point(face_uv_to_xyz(
        face,
        st_to_uv(siti_to_st(si)),
        st_to_uv(siti_to_st(ti)),
    ))
}

#[cfg(test)]
fn siti_to_level(si: u64) -> i8 {
    (MAX_LEVEL as i8) - ((si | MAX_SITI).trailing_zeros() as i8)
}

#[cfg(test)]
/// xyz_to_face_siti transforms the (not necessarily unit length) Point to
/// (face, si, ti) coordinates and the level the Point is at.
fn xyz_to_face_siti(p: &Point) -> (u8, u64, u64, i8) {
    let (face, u, v) = xyz_to_face_uv(&p.0);
    let si = st_to_siti(uv_to_st(u));
    let ti = st_to_siti(uv_to_st(v));

    // If the levels corresponding to si,ti are not equal, then p is not a cell
    // center. The si,ti values of 0 and maxSiTi need to be handled specially
    // because they do not correspond to cell centers at any valid level; they
    // are mapped to level -1 by the code at the end.
    let level = siti_to_level(si);
    if level < 0 || level != siti_to_level(ti) {
        return (face, si, ti, -1);
    }

    // In infinite precision, this test could be changed to ST == SiTi. However,
    // due to rounding errors, uvToST(xyzToFaceUV(faceUVToXYZ(stToUV(...)))) is
    // not idempotent. On the other hand, the center is computed exactly the same
    // way p was originally computed (if it is indeed the center of a Cell);
    // the comparison can be exact.
    if p.0 == face_siti_to_xyz(face, si, ti).0.normalize() {
        (face, si, ti, level)
    } else {
        (face, si, ti, -1)
    }
}

pub fn unorm(face: u8, u: f64) -> Vector {
    match face {
        0 => Vector::new(u, -1., 0.),
        1 => Vector::new(1., u, 0.),
        2 => Vector::new(1., 0., u),
        3 => Vector::new(-u, 0., 1.),
        4 => Vector::new(0., -u, 1.),
        5 => Vector::new(0., -1., -u),
        _ => unimplemented!(),
    }
}

pub fn vnorm(face: u8, v: f64) -> Vector {
    match face {
        0 => Vector::new(-v, 0., 1.),
        1 => Vector::new(0., -v, 1.),
        2 => Vector::new(0., -1., -v),
        3 => Vector::new(v, -1., 0.),
        4 => Vector::new(1., v, 0.),
        5 => Vector::new(1., 0., v),
        _ => unimplemented!(),
    }
}

macro_rules! V {
    ($x:expr, $y:expr, $z:expr) => {
        Vector {
            x: $x as f64,
            y: $y as f64,
            z: $z as f64,
        }
    };
}
macro_rules! P {
    ($x:expr, $y:expr, $z:expr) => {
        Point(V!($x, $y, $z))
    };
}

const FACE_UVW_AXES: [[Point; 3]; 6] = [
    [P!(0, 1, 0), P!(0, 0, 1), P!(1, 0, 0)],
    [P!(-1, 0, 0), P!(0, 0, 1), P!(0, 1, 0)],
    [P!(-1, 0, 0), P!(0, -1, 0), P!(0, 0, 1)],
    [P!(0, 0, -1), P!(0, -1, 0), P!(-1, 0, 0)],
    [P!(0, 0, -1), P!(1, 0, 0), P!(0, -1, 0)],
    [P!(0, 1, 0), P!(1, 0, 0), P!(0, 0, -1)],
];

#[cfg(test)]
const FACE_UVW_FACES: [[[u8; 2]; 3]; 6] = [
    [[4, 1], [5, 2], [3, 0]],
    [[0, 3], [5, 2], [4, 1]],
    [[0, 3], [1, 4], [5, 2]],
    [[2, 5], [1, 4], [0, 3]],
    [[2, 5], [3, 0], [1, 4]],
    [[4, 1], [3, 0], [2, 5]],
];

fn uvw_axis(face: u8, axis: u8) -> Point {
    FACE_UVW_AXES[face as usize][axis as usize]
}

#[cfg(test)]
fn uvw_face(face: u8, axis: u8, direction: u8) -> u8 {
    FACE_UVW_FACES[face as usize][axis as usize][direction as usize]
}

pub fn u_axis(face: u8) -> Point {
    uvw_axis(face, 0)
}

pub fn v_axis(face: u8) -> Point {
    uvw_axis(face, 1)
}

#[cfg(test)]
fn unit_norm(face: u8) -> Point {
    uvw_axis(face, 2)
}

pub const SWAP_MASK: u8 = 0x01;

#[cfg(test)]
mod tests {
    extern crate rand;

    use self::rand::Rng;
    use super::*;
    use crate::r3::vector::Axis;
    use crate::s2::random;
    use std;

    #[test]
    fn st_uv() {
        assert_eq!(0.125, st_to_uv(uv_to_st(0.125)));
        assert_eq!(0.125, uv_to_st(st_to_uv(0.125)));
    }

    #[test]
    fn test_uv_norms() {
        let step = 1. / 1024.;
        for face in 0..6 {
            let mut x = -1.;
            loop {
                let angle = face_uv_to_xyz(face, x, -1.)
                    .cross(&face_uv_to_xyz(face, x, 1.))
                    .angle(&unorm(face, x));
                assert!(angle.rad() < std::f64::EPSILON);

                x += step;
                if x > 1. {
                    break;
                }
            }
        }
    }

    #[test]
    fn test_face_uv_to_xyz() {
        let mut sum = V!(0., 0., 0.);

        for face in 0..6 {
            let center = face_uv_to_xyz(face, 0., 0.);
            assert!(center.approx_eq(&unit_norm(face).0));

            match center.largest_component() {
                Axis::X => assert_eq!(center.x.abs(), 1.0),
                Axis::Y => assert_eq!(center.y.abs(), 1.0),
                Axis::Z => assert_eq!(center.z.abs(), 1.0),
            }

            //TODO: implement += operator?
            sum = sum + center.abs();

            assert_eq!(
                u_axis(face)
                    .0
                    .cross(&v_axis(face).0)
                    .dot(&unit_norm(face).0),
                1.0
            );

            let sign = if face & SWAP_MASK == 1 {
                -1.0f64
            } else {
                1.0f64
            };

            assert_eq!(
                face_uv_to_xyz(face, sign, -sign),
                face_uv_to_xyz((face + 1) % 6, -1., -1.)
            );
        }

        assert!(sum.approx_eq(&V!(2., 2., 2.)));
    }

    fn test_face_xyz_to_uv_case(face: u8, point: &Point, expected: (f64, f64, bool)) {
        if let Some((u, v)) = face_xyz_to_uv(face, point) {
            assert!((u - expected.0) <= std::f64::EPSILON);
            assert!((v - expected.1) <= std::f64::EPSILON);
            assert_eq!(true, expected.2);
        } else {
            assert_eq!(false, expected.2);
        }
    }

    #[test]
    fn test_face_xyz_to_uv() {
        let point = P!(1.1, 1.2, 1.3);
        let point_neg = P!(-1.1, -1.2, -1.3);

        test_face_xyz_to_uv_case(0, &point, (1. + 1. / 11., 1. + 2. / 11., true));
        test_face_xyz_to_uv_case(0, &point_neg, (0., 0., false));
        test_face_xyz_to_uv_case(1, &point, (-11. / 12., 1. + 1. / 12., true));
        test_face_xyz_to_uv_case(1, &point_neg, (0., 0., false));
        test_face_xyz_to_uv_case(2, &point, (-11. / 13., -12. / 13., true));
        test_face_xyz_to_uv_case(2, &point_neg, (0., 0., false));
        test_face_xyz_to_uv_case(3, &point, (0., 0., false));
        test_face_xyz_to_uv_case(3, &point_neg, (1. + 2. / 11., 1. + 1. / 11., true));
        test_face_xyz_to_uv_case(4, &point, (0., 0., false));
        test_face_xyz_to_uv_case(4, &point_neg, (1. + 1. / 12., -11. / 12., true));
        test_face_xyz_to_uv_case(5, &point, (0., 0., false));
        test_face_xyz_to_uv_case(5, &point_neg, (-12. / 13., -11. / 13., true));
    }

    #[test]
    fn test_face_xyz_to_uvw() {
        let origin = P!(0., 0., 0.);
        let pos_x = P!(1., 0., 0.);
        let neg_x = P!(-1., 0., 0.);
        let pos_y = P!(0., 1., 0.);
        let neg_y = P!(0., -1., 0.);
        let pos_z = P!(0., 0., 1.);
        let neg_z = P!(0., 0., -1.);

        for face in 0..6 {
            assert_eq!(origin, face_xyz_to_uvw(face, &origin));

            assert_eq!(pos_x, face_xyz_to_uvw(face, &u_axis(face)));
            assert_eq!(neg_x, face_xyz_to_uvw(face, &(u_axis(face) * -1.)));

            assert_eq!(pos_y, face_xyz_to_uvw(face, &v_axis(face)));
            assert_eq!(neg_y, face_xyz_to_uvw(face, &(v_axis(face) * -1.)));

            assert_eq!(pos_z, face_xyz_to_uvw(face, &unit_norm(face)));
            assert_eq!(neg_z, face_xyz_to_uvw(face, &(unit_norm(face) * -1.)));
        }
    }

    #[test]
    fn test_uvw_axis() {
        for face in 0..6 {
            assert_eq!(
                face_uv_to_xyz(face, 1., 0.) - face_uv_to_xyz(face, 0., 0.),
                u_axis(face).0
            );
            assert_eq!(
                face_uv_to_xyz(face, 0., 1.) - face_uv_to_xyz(face, 0., 0.),
                v_axis(face).0
            );
            assert_eq!(face_uv_to_xyz(face, 0., 0.), unit_norm(face).0);

            assert_eq!(
                1.,
                u_axis(face)
                    .0
                    .cross(&v_axis(face).0)
                    .dot(&unit_norm(face).0)
            );
            assert_eq!(u_axis(face), uvw_axis(face, 0));
            assert_eq!(v_axis(face), uvw_axis(face, 1));
            assert_eq!(unit_norm(face), uvw_axis(face, 2));
        }
    }

    #[test]
    fn test_siti_st_roundtrip() {
        let mut rng = random::rng();
        for _ in 0..1000 {
            let si = rng.gen_range(0, MAX_SITI);
            assert_eq!(st_to_siti(siti_to_st(si)), si);
        }

        for _ in 0..1000 {
            let st = rng.gen_range(0., 1f64);
            let error = siti_to_st(st_to_siti(st)) - st;
            assert!(error.abs() < (1. / MAX_LEVEL as f64));
        }
    }

    #[test]
    fn test_uvw_face() {
        for f in 0..6 {
            for axis in 0..3 {
                assert_eq!(face(&(uvw_axis(f, axis).0 * -1.)), uvw_face(f, axis, 0));
                assert_eq!(face(&uvw_axis(f, axis).0), uvw_face(f, axis, 1));
            }
        }
    }

    #[test]
    fn test_xyz_to_face_siti() {
        let mut rng = random::rng();
        let shift = Point(Vector::new(1e-13, 1e-13, 1e-13));

        for level in 0..MAX_LEVEL {
            for _ in 0..1000 {
                let ci = random::cellid_for_level(&mut rng, level);

                let (f, si, ti, gotlevel) = xyz_to_face_siti(&Point::from(&ci));
                assert_eq!(gotlevel, level as i8);

                assert_eq!(
                    ci,
                    CellID::from_face_ij(f, (si / 2) as i32, (ti / 2) as i32).parent(level)
                );

                //TODO: add by ref
                let p_moved = Point::from(ci) + shift.clone();
                let (f_moved, si_moved, ti_moved, gotlevel_moved) = xyz_to_face_siti(&p_moved);

                assert_eq!(gotlevel_moved, -1);
                assert_eq!(f, f_moved);

                assert_eq!(si, si_moved);
                assert_eq!(ti, ti_moved);
            }

            {
                let face_random = rng.gen_range(0, NUM_FACES);
                let mask = (std::u64::MAX << (MAX_LEVEL - level)) & (MAX_SITI - 1);
                let si_random = rng.gen_range(0, MAX_SITI) & mask;
                let ti_random = rng.gen_range(0, MAX_SITI) & mask;

                let lower_mask = (1 << (MAX_LEVEL - level)) - 1;
                assert!(si_random < MAX_SITI && (si_random & lower_mask) == 0);
                assert!(ti_random < MAX_SITI && (ti_random & lower_mask) == 0);

                let p_random = face_siti_to_xyz(face_random, si_random, ti_random);
                let (f, si, ti, gotlevel) = xyz_to_face_siti(&p_random);

                if f != face_random {
                    assert_eq!(-1, gotlevel);
                    assert!(si == 0 || si == MAX_SITI || ti == 0 || ti == MAX_SITI);
                } else {
                    assert_eq!(si, si_random);
                    assert_eq!(ti, ti_random);
                    if gotlevel >= 0 {
                        assert!(p_random.approx_eq(
                            &CellID::from_face_ij(f, si as i32 / 2, ti as i32 / 2)
                                .parent(gotlevel as u64)
                                .into()
                        ));
                    }
                }
            }
        }
    }

    #[test]
    fn test_xyz_face_siti_roundtrip() {
        let mut rng = random::rng();

        for level in 0..MAX_LEVEL {
            for _ in 0..1000 {
                let ci = random::cellid_for_level(&mut rng, level);
                let p = Point::from(&ci);
                let (f, si, ti, _) = xyz_to_face_siti(&p);
                let op = face_siti_to_xyz(f, si, ti);
                assert!(op.approx_eq(&p));
            }
        }
    }
}
