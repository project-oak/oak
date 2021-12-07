use crate::consts::remainder;
use crate::r3::vector::Vector;
use crate::s1::*;
use crate::s2::point::Point;
use std;
use std::f64::consts::PI;

//TODO: typed const?
const NORTH_POLE_LAT: f64 = PI / 2.;
const SOUTH_POLE_LAT: f64 = PI / -2.;

#[derive(Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct LatLng {
    pub lat: Angle,
    pub lng: Angle,
}

impl std::fmt::Debug for LatLng {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "[{:?}, {:?}]", self.lat, self.lng)
    }
}

impl LatLng {
    pub fn new(lat: Angle, lng: Angle) -> Self {
        LatLng { lat, lng }
    }

    pub fn is_valid(&self) -> bool {
        self.lat.rad().abs() <= PI / 2. && self.lng.rad().abs() <= PI
    }

    pub fn normalized(&self) -> Self {
        let lat = if self.lat.rad() > NORTH_POLE_LAT {
            Rad(NORTH_POLE_LAT).into()
        } else if self.lat.rad() < SOUTH_POLE_LAT {
            Rad(SOUTH_POLE_LAT).into()
        } else {
            self.lat
        };

        LatLng {
            lat,
            lng: Rad(remainder(self.lng.rad(), PI * 2.)).into(),
        }
    }

    pub fn distance(&self, other: &Self) -> Angle {
        let dlat = (0.5 * (other.lat.rad() - self.lat.rad())).sin();
        let dlng = (0.5 * (other.lng.rad() - self.lng.rad())).sin();

        let x = dlat * dlat + dlng * dlng * self.lat.rad().cos() * other.lat.rad().cos();
        Rad(2. * x.sqrt().atan2((1. - x).max(0.).sqrt())).into()
    }
}

impl Point {
    pub fn latitude(&self) -> Angle {
        let v = &self.0;
        let l = (v.x * v.x + v.y * v.y).sqrt();
        Rad(v.z.atan2(l)).into()
    }

    pub fn longitude(&self) -> Angle {
        let v = &self.0;
        Rad(v.y.atan2(v.x)).into()
    }
}

impl<'a> From<&'a LatLng> for Point {
    fn from(ll: &'a LatLng) -> Self {
        let phi = ll.lat.rad();
        let theta = ll.lng.rad();
        let cosphi = phi.cos();
        Point(Vector {
            x: theta.cos() * cosphi,
            y: theta.sin() * cosphi,
            z: phi.sin(),
        })
    }
}
impl From<LatLng> for Point {
    fn from(ll: LatLng) -> Self {
        Self::from(&ll)
    }
}

impl<'a> From<&'a Point> for LatLng {
    fn from(p: &'a Point) -> Self {
        LatLng {
            lat: p.latitude(),
            lng: p.longitude(),
        }
    }
}
impl From<Point> for LatLng {
    fn from(p: Point) -> Self {
        LatLng::from(&p)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r3::vector::Vector;
    use crate::s1;
    use crate::s2::point::Point;

    macro_rules! ll {
        ($lat:expr, $lng:expr) => {
            LatLng {
                lat: s1::Deg($lat).into(),
                lng: s1::Deg($lng).into(),
            }
        };
    }
    macro_rules! p {
        ($x:expr, $y:expr, $z:expr) => {
            Point(Vector {
                x: $x as f64,
                y: $y as f64,
                z: $z as f64,
            })
        };
    }

    fn test_latlng_normalized_case(descr: &str, pos: LatLng, want: LatLng) {
        let desc: String = descr.into();
        let normalized = pos.normalized();
        assert!(normalized.is_valid(), desc);

        let distance = normalized.distance(&want);
        assert!(distance < s1::Deg(1e-13).into(), desc);
    }

    #[test]
    fn test_latlng_normalized() {
        test_latlng_normalized_case(
            &"Valid lat/lng",
            ll!(21.8275043, 151.1979675),
            ll!(21.8275043, 151.1979675),
        );
        test_latlng_normalized_case(
            &"Valid lat/lng in the West",
            ll!(21.8275043, -151.1979675),
            ll!(21.8275043, -151.1979675),
        );
        test_latlng_normalized_case(
            &"Beyond the North pole",
            ll!(95., 151.1979675),
            ll!(90., 151.1979675),
        );
        test_latlng_normalized_case(
            "Beyond the South pole",
            ll!(-95., 151.1979675),
            ll!(-90., 151.1979675),
        );
        test_latlng_normalized_case(
            "At the date line (from East)",
            ll!(21.8275043, 180.),
            ll!(21.8275043, 180.),
        );
        test_latlng_normalized_case(
            "At the date line (from West)",
            ll!(21.8275043, -180.),
            ll!(21.8275043, -180.),
        );
        test_latlng_normalized_case(
            "Across the date line going East",
            ll!(21.8275043, 181.0012),
            ll!(21.8275043, -178.9988),
        );
        test_latlng_normalized_case(
            "Across the date line going West",
            ll!(21.8275043, -181.0012),
            ll!(21.8275043, 178.9988),
        );
        test_latlng_normalized_case("All wrong", ll!(256., 256.), ll!(90., -104.));
    }

    fn test_approx_eq(a: f64, b: f64) {
        assert!((a - b).abs() < 1e-14);
    }

    fn test_latlng_point_conversion_case(ll: LatLng, p: Point) {
        //TODO
        let llp: Point = ll.clone().into();
        test_approx_eq(llp.0.x, p.0.x);
        test_approx_eq(llp.0.y, p.0.y);
        test_approx_eq(llp.0.z, p.0.z);

        let pll: LatLng = p.into();
        test_approx_eq(pll.lat.rad(), ll.lat.rad());
        let is_polar = ll.lng.rad() == PI / 2. || ll.lng.rad() == PI / -2.;
        if !is_polar {
            test_approx_eq(pll.lng.rad(), ll.lng.rad());
        }
    }

    #[test]
    fn test_latlng_point_conversion() {
        test_latlng_point_conversion_case(ll!(0., 0.), p!(1, 0, 0));
        test_latlng_point_conversion_case(ll!(90., 0.), p!(6.12323e-17, 0, 1));
        test_latlng_point_conversion_case(ll!(-90., 0.), p!(6.12323e-17, 0, -1));
        test_latlng_point_conversion_case(ll!(0., 180.), p!(-1, 1.22465e-16, 0));
        test_latlng_point_conversion_case(ll!(0., -180.), p!(-1, -1.22465e-16, 0));
        test_latlng_point_conversion_case(ll!(90., 180.), p!(-6.12323e-17, 7.4988e-33, 1));
        test_latlng_point_conversion_case(ll!(90., -180.), p!(-6.12323e-17, -7.4988e-33, 1));
        test_latlng_point_conversion_case(ll!(-90., 180.), p!(-6.12323e-17, 7.4988e-33, -1));
        test_latlng_point_conversion_case(ll!(-90., -180.), p!(-6.12323e-17, -7.4988e-33, -1));
        test_latlng_point_conversion_case(
            ll!(-81.82750430354997, 151.19796752929685),
            p!(-0.12456788151479525, 0.0684875268284729, -0.989844584550441),
        );
    }

    fn test_latlng_distance_case(ll1: LatLng, ll2: LatLng, want: f64, tolerance: f64) {
        let distance: s1::Deg = ll1.distance(&ll2).into();
        assert!((distance.0 - want).abs() <= tolerance);
    }

    #[test]
    fn test_latlng_distance() {
        test_latlng_distance_case(ll!(90., 0.), ll!(90., 0.), 0., 0.);
        test_latlng_distance_case(ll!(-37., 25.), ll!(-66., -155.), 77., 1e-13);
        test_latlng_distance_case(ll!(0., 165.), ll!(0., -80.), 115., 1e-13);
        test_latlng_distance_case(ll!(47., -127.), ll!(-47., 53.), 180., 2e-6);
    }
}
