use std;
use std::f64::consts::PI;

use crate::consts::*;
use crate::r1;
use crate::s1::*;
use crate::s2::edgeutil;
use crate::s2::latlng::LatLng;

#[derive(Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Rect {
    pub lat: r1::interval::Interval,
    pub lng: Interval,
}

impl std::fmt::Debug for Rect {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "[lo{:?}, hi{:?}]", self.lo(), self.hi())
    }
}

const VALID_RECT_LAT_RANGE: r1::interval::Interval = r1::interval::Interval {
    lo: -PI / 2.,
    hi: PI / 2.,
};
const VALID_RECT_LNG_RANGE: Interval = interval::FULL;

impl Rect {
    pub fn empty() -> Rect {
        Rect {
            lat: r1::interval::EMPTY,
            lng: interval::EMPTY,
        }
    }

    pub fn full() -> Rect {
        Rect {
            lat: VALID_RECT_LAT_RANGE,
            lng: VALID_RECT_LNG_RANGE,
        }
    }

    pub fn from_center_size(center: LatLng, size: LatLng) -> Self {
        let half = LatLng {
            lat: size.lat * 0.5,
            lng: size.lng * 0.5,
        };
        Rect::from(center).expanded(&half)
    }

    pub fn is_valid(&self) -> bool {
        self.lat.lo.abs() <= PI / 2.
            && self.lat.hi <= PI / 2.
            && self.lng.is_valid()
            && self.lat.is_empty() == self.lng.is_empty()
    }

    pub fn is_empty(&self) -> bool {
        self.lat.is_empty()
    }

    pub fn is_full(&self) -> bool {
        self.lat == VALID_RECT_LAT_RANGE && self.lng.is_full()
    }

    pub fn is_point(&self) -> bool {
        self.lat.lo == self.lat.hi && self.lng.lo == self.lng.hi
    }

    pub fn vertex(&self, i: u8) -> LatLng {
        let (lat, lng) = match i {
            0 => (self.lat.lo, self.lng.lo),
            1 => (self.lat.lo, self.lng.hi),
            2 => (self.lat.hi, self.lng.hi),
            3 => (self.lat.hi, self.lng.lo),
            _ => unimplemented!(),
        };
        LatLng {
            lat: Rad(lat).into(),
            lng: Rad(lng).into(),
        }
    }

    pub fn lo(&self) -> LatLng {
        self.vertex(0)
    }
    pub fn hi(&self) -> LatLng {
        self.vertex(2)
    }
    pub fn center(&self) -> LatLng {
        LatLng {
            lat: Rad(self.lat.center()).into(),
            lng: Rad(self.lng.center()).into(),
        }
    }
    pub fn size(&self) -> LatLng {
        LatLng {
            lat: Rad(self.lat.len()).into(),
            lng: Rad(self.lng.len()).into(),
        }
    }

    pub fn area(&self) -> f64 {
        if self.is_empty() {
            0.
        } else {
            let cap_diff = (self.lat.hi.sin() - self.lat.lo.sin()).abs();
            self.lng.len() * cap_diff
        }
    }

    pub fn expanded(&self, margin: &LatLng) -> Self {
        let lat = self.lat.expanded(margin.lat.rad());
        let lng = self.lng.expanded(margin.lng.rad());

        if lat.is_empty() || lng.is_empty() {
            Self::empty()
        } else {
            Rect {
                lat: lat.intersection(&VALID_RECT_LAT_RANGE),
                lng,
            }
        }
    }

    pub fn polar_closure(&self) -> Self {
        if self.lat.lo == -PI / 2. || self.lat.hi == PI / 2. {
            Rect {
                lat: self.lat,
                lng: interval::FULL,
            }
        } else {
            self.clone()
        }
    }

    pub fn union(&self, other: &Self) -> Self {
        Rect {
            lat: self.lat.union(&other.lat),
            lng: self.lng.union(&other.lng),
        }
    }

    pub fn intersection(&self, other: &Self) -> Self {
        let lat = self.lat.intersection(&other.lat);
        let lng = self.lng.intersection(&other.lng);

        if lat.is_empty() || lng.is_empty() {
            Self::empty()
        } else {
            Rect { lat, lng }
        }
    }

    pub fn intersects(&self, other: &Rect) -> bool {
        self.lat.intersects(&other.lat) && self.lng.intersects(&other.lng)
    }

    // extra functions
    pub fn approx_eq(&self, other: &Self) -> bool {
        f64_eq(self.lat.lo, other.lat.lo)
            && f64_eq(self.lat.hi, other.lat.hi)
            && f64_eq(self.lng.lo, other.lng.lo)
            && f64_eq(self.lng.hi, other.lng.hi)
    }
}

impl<'a, 'b> std::ops::Add<&'a LatLng> for &'b Rect {
    type Output = Rect;
    fn add(self, ll: &'a LatLng) -> Self::Output {
        if !ll.is_valid() {
            self.clone()
        } else {
            Rect {
                lat: self.lat + ll.lat.rad(),
                lng: self.lng + ll.lng.rad(),
            }
        }
    }
}

impl From<LatLng> for Rect {
    fn from(ll: LatLng) -> Self {
        Self {
            lat: r1::interval::Interval::from_point(ll.lat.rad()),
            lng: Interval {
                lo: ll.lng.rad(),
                hi: ll.lng.rad(),
            },
        }
    }
}

use crate::s2::cap::Cap;
use crate::s2::cell::Cell;
use crate::s2::point::Point;
use crate::s2::region::Region;

impl Region for Rect {
    /// cap_bound returns a cap that countains Rect.
    fn cap_bound(&self) -> Cap {
        // We consider two possible bounding caps, one whose axis passes
        // through the center of the lat-long rectangle and one whose axis
        // is the north or south pole.  We return the smaller of the two caps.

        if self.is_empty() {
            return Cap::empty();
        }

        let (pole_z, pole_angle) = if self.lat.hi + self.lat.lo < 0. {
            // South pole axis yields smaller cap.
            (-1., PI / 2. + self.lat.hi)
        } else {
            (1., PI / 2. - self.lat.lo)
        };

        let pole_cap =
            Cap::from_center_angle(&Point::from_coords(0., 0., pole_z), &Rad(pole_angle).into());

        // For bounding rectangles that span 180 degrees or less in longitude, the
        // maximum cap size is achieved at one of the rectangle vertices.  For
        // rectangles that are larger than 180 degrees, we punt and always return a
        // bounding cap centered at one of the two poles.
        if remainder(self.lng.hi - self.lng.lo, 2. * PI) >= 0.
            && self.lng.hi - self.lng.lo < 2. * PI
        {
            let mid_cap = Cap::from(&Point::from(self.center()))
                + Point::from(self.lo())
                + Point::from(self.hi());

            if mid_cap.height() < pole_cap.height() {
                return mid_cap;
            }
        }
        pole_cap
    }

    /// rect_bound returns itself.
    fn rect_bound(&self) -> Rect {
        self.clone()
    }

    /// contains_cell reports whether the given Cell is contained by this Rect.
    fn contains_cell(&self, c: &Cell) -> bool {
        // A latitude-longitude rectangle contains a cell if and only if it contains
        // the cell's bounding rectangle. This test is exact from a mathematical
        // point of view, assuming that the bounds returned by Cell.RectBound()
        // are tight. However, note that there can be a loss of precision when
        // converting between representations -- for example, if an s2.Cell is
        // converted to a polygon, the polygon's bounding rectangle may not contain
        // the cell's bounding rectangle. This has some slightly unexpected side
        // effects; for instance, if one creates an s2.Polygon from an s2.Cell, the
        // polygon will contain the cell, but the polygon's bounding box will not.
        self.contains(&c.rect_bound())
    }

    fn intersects_cell(&self, cell: &Cell) -> bool {
        if self.is_empty() {
            return false;
        }

        if self.contains_point(&Point(cell.id.raw_point())) {
            return true;
        }

        if cell.contains_point(&Point::from(self.center())) {
            return true;
        }

        // Quick rejection test (not required for correctness).
        if !self.intersects(&cell.rect_bound()) {
            return false;
        }

        // Precompute the cell vertices as points and latitude-longitudes. We also
        // check whether the Cell contains any corner of the rectangle, or
        // vice-versa, since the edge-crossing tests only check the edge interiors.
        let mut vertices = Vec::new();
        let mut latlngs = Vec::new();

        for i in 0..4 {
            vertices.push(cell.vertex(i));
            latlngs.push(LatLng::from(vertices[i]));

            if self.contains_latlng(&latlngs[i]) {
                return true;
            }
            if cell.contains_point(&Point::from(self.vertex(i as u8))) {
                return true;
            }
        }

        // Now check whether the boundaries intersect. Unfortunately, a
        // latitude-longitude rectangle does not have straight edges: two edges
        // are curved, and at least one of them is concave.
        for i in 0..4 {
            let edge_lng =
                interval::Interval::new(latlngs[i].lng.rad(), latlngs[(i + 1) & 3].lng.rad());
            if !self.lng.intersects(&edge_lng) {
                continue;
            }

            let a = &vertices[i];
            let b = &vertices[(i + 1) & 3];
            if edge_lng.contains(self.lng.lo)
                && intersects_lng_edge(a, b, self.lat, Rad(self.lng.lo).into())
            {
                return true;
            }
            if edge_lng.contains(self.lng.hi)
                && intersects_lng_edge(a, b, self.lat, Rad(self.lng.hi).into())
            {
                return true;
            }
            if intersects_lat_edge(a, b, Rad(self.lat.lo).into(), self.lng) {
                return true;
            }
            if intersects_lat_edge(a, b, Rad(self.lat.hi).into(), self.lng) {
                return true;
            }
        }

        return false;
    }
}

// intersectsLatEdge reports whether the edge AB intersects the given edge of constant
// latitude. Requires the points to have unit length.
fn intersects_lat_edge(a: &Point, b: &Point, lat: Angle, lng: interval::Interval) -> bool {
    // Unfortunately, lines of constant latitude are curves on
    // the sphere. They can intersect a straight edge in 0, 1, or 2 points.

    // First, compute the normal to the plane AB that points vaguely north.
    let mut z = a.cross(b).normalize();
    if z.0.z < 0. {
        z = Point(z.0 * -1.)
    }

    // Extend this to an orthonormal frame (x,y,z) where x is the direction
    // where the great circle through AB achieves its maximium latitude.
    let y = z.cross(&Point::from_coords(0., 0., 1.)).normalize();
    let x = y.cross(&z);

    // Compute the angle "theta" from the x-axis (in the x-y plane defined
    // above) where the great circle intersects the given line of latitude.
    let sin_lat = lat.rad().sin();
    if sin_lat.abs() >= x.0.z {
        // The great circle does not reach the given latitude.
        return false;
    }

    let cos_theta = sin_lat / x.0.z;
    let sin_theta = (1. - cos_theta * cos_theta).sqrt();
    let theta = sin_theta.atan2(cos_theta);

    // The candidate intersection points are located +/- theta in the x-y
    // plane. For an intersection to be valid, we need to check that the
    // intersection point is contained in the interior of the edge AB and
    // also that it is contained within the given longitude interval "lng".

    // Compute the range of theta values spanned by the edge AB.
    let ab_theta = interval::Interval::from_point_pair(
        a.0.dot(&y.0).atan2(a.0.dot(&x.0)),
        b.0.dot(&y.0).atan2(b.0.dot(&x.0)),
    );

    if ab_theta.contains(theta) {
        // Check if the intersection point is also in the given lng interval.
        let isect = (x * cos_theta) + (y * sin_theta);
        if lng.contains(isect.0.y.atan2(isect.0.x)) {
            return true;
        }
    }

    if ab_theta.contains(-theta) {
        // Check if the other intersection point is also in the given lng interval.
        let isect = (x * cos_theta) - (y * sin_theta);
        if lng.contains(isect.0.y.atan2(isect.0.x)) {
            return true;
        }
    }

    return false;
}

fn intersects_lng_edge(a: &Point, b: &Point, lat: r1::interval::Interval, lng: Angle) -> bool {
    // The nice thing about edges of constant longitude is that
    // they are straight lines on the sphere (geodesics).
    edgeutil::simple_crossing(
        a,
        b,
        &Point::from(LatLng::new(Rad(lat.lo).into(), lng)),
        &Point::from(LatLng::new(Rad(lat.hi).into(), lng)),
    )
}

impl Rect {
    /// contains reports whether this Rect contains the other Rect.
    pub fn contains(&self, other: &Self) -> bool {
        self.lat.contains_interval(&other.lat) && self.lng.contains_interval(&other.lng)
    }

    /// contains_latlng reports whether the given LatLng is within the Rect.
    pub fn contains_latlng(&self, ll: &LatLng) -> bool {
        ll.is_valid() && self.lat.contains(ll.lat.rad()) && self.lng.contains(ll.lng.rad())
    }

    /// contains_point reports whether the given Point is within the Rect.
    pub fn contains_point(&self, p: &Point) -> bool {
        self.contains_latlng(&LatLng::from(p))
    }
}

/*

// IntersectsCell reports whether this rectangle intersects the given cell. This is an
// exact test and may be fairly expensive.
func (r Rect) IntersectsCell(c Cell) bool {
    // First we eliminate the cases where one region completely contains the
    // other. Once these are disposed of, then the regions will intersect
    // if and only if their boundaries intersect.
    if r.IsEmpty() {
        return false
    }
    if r.ContainsPoint(Point{c.id.rawPoint()}) {
        return true
    }
    if c.ContainsPoint(PointFromLatLng(r.Center())) {
        return true
    }

    // Quick rejection test (not required for correctness).
    if !r.Intersects(c.RectBound()) {
        return false
    }

    // Precompute the cell vertices as points and latitude-longitudes. We also
    // check whether the Cell contains any corner of the rectangle, or
    // vice-versa, since the edge-crossing tests only check the edge interiors.
    vertices := [4]Point{}
    latlngs := [4]LatLng{}

    for i := range vertices {
        vertices[i] = c.Vertex(i)
        latlngs[i] = LatLngFromPoint(vertices[i])
        if r.ContainsLatLng(latlngs[i]) {
            return true
        }
        if c.ContainsPoint(PointFromLatLng(r.Vertex(i))) {
            return true
        }
    }

    // Now check whether the boundaries intersect. Unfortunately, a
    // latitude-longitude rectangle does not have straight edges: two edges
    // are curved, and at least one of them is concave.
    for i := range vertices {
        edgeLng := s1.IntervalFromEndpoints(latlngs[i].Lng.Radians(), latlngs[(i+1)&3].Lng.Radians())
        if !r.Lng.Intersects(edgeLng) {
            continue
        }

        a := vertices[i]
        b := vertices[(i+1)&3]
        if edgeLng.Contains(r.Lng.Lo) && intersectsLngEdge(a, b, r.Lat, s1.Angle(r.Lng.Lo)) {
            return true
        }
        if edgeLng.Contains(r.Lng.Hi) && intersectsLngEdge(a, b, r.Lat, s1.Angle(r.Lng.Hi)) {
            return true
        }
        if intersectsLatEdge(a, b, s1.Angle(r.Lat.Lo), r.Lng) {
            return true
        }
        if intersectsLatEdge(a, b, s1.Angle(r.Lat.Hi), r.Lng) {
            return true
        }
    }
    return false
}

// BUG: The major differences from the C++ version are:
//   - GetCentroid, Get*Distance, Vertex, InteriorContains(LatLng|Rect|Point)
*/
