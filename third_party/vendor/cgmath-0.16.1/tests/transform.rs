// Copyright 2014 The CGMath Developers. For a full listing of the authors,
// refer to the Cargo.toml file at the top-level directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#[macro_use]
extern crate approx;
extern crate cgmath;

#[cfg(feature = "serde")]
extern crate serde_json;

use cgmath::*;

#[test]
fn test_invert() {
    let v = Vector3::new(1.0f64, 2.0, 3.0);
    let t = Decomposed {
        scale: 1.5f64,
        rot: Quaternion::new(0.5f64, 0.5, 0.5, 0.5),
        disp: Vector3::new(6.0f64, -7.0, 8.0),
    };
    let ti = t.inverse_transform()
        .expect("Expected successful inversion");
    let vt = t.transform_vector(v);
    assert_ulps_eq!(&v, &ti.transform_vector(vt));
}

#[test]
fn test_inverse_vector() {
    let v = Vector3::new(1.0f64, 2.0, 3.0);
    let t = Decomposed {
        scale: 1.5f64,
        rot: Quaternion::new(0.5f64, 0.5, 0.5, 0.5),
        disp: Vector3::new(6.0f64, -7.0, 8.0),
    };
    let vt = t.inverse_transform_vector(v)
        .expect("Expected successful inversion");
    assert_ulps_eq!(v, t.transform_vector(vt));
}

#[test]
fn test_look_at() {
    let eye = Point3::new(0.0f64, 0.0, -5.0);
    let center = Point3::new(0.0f64, 0.0, 0.0);
    let up = Vector3::new(1.0f64, 0.0, 0.0);
    let t: Decomposed<Vector3<f64>, Quaternion<f64>> = Transform::look_at(eye, center, up);
    let point = Point3::new(1.0f64, 0.0, 0.0);
    let view_point = Point3::new(0.0f64, 1.0, 5.0);
    assert_ulps_eq!(&t.transform_point(point), &view_point);
}

#[cfg(feature = "serde")]
#[test]
fn test_serialize() {
    let t = Decomposed {
        scale: 1.5f64,
        rot: Quaternion::new(0.5f64, 0.5, 0.5, 0.5),
        disp: Vector3::new(6.0f64, -7.0, 8.0),
    };

    let serialized = serde_json::to_string(&t).unwrap();
    let deserialized: Decomposed<Vector3<f64>, Quaternion<f64>> =
        serde_json::from_str(&serialized).unwrap();

    assert_ulps_eq!(&t, &deserialized);
}
