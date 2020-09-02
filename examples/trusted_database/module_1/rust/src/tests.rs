//
// Copyright 2020 The Project Oak Authors
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
//

use crate::{distance, proto::oak::examples::trusted_database::Location};

fn get_distance(first: (f32, f32), second: (f32, f32)) -> f32 {
    distance(
        Location {
            latitude_degrees: first.0,
            longitude_degrees: first.1,
        },
        Location {
            latitude_degrees: second.0,
            longitude_degrees: second.1,
        },
    )
}

fn assert_approx_eq(left: f32, right: f32) {
    if (left - right).abs() > 0.000001 {
        panic!("{} is not equal to {}", left, right);
    }
}

#[test]
fn test_distance() {
    assert_approx_eq(get_distance((0.0, 0.0), (0.0, 0.0)), 0.0);
    assert_approx_eq(get_distance((0.0, 0.0), (10.0, 10.0)), 1568.5204);
    assert_approx_eq(get_distance((10.0, 10.0), (-10.0, -10.0)), 3137.0413);
    assert_approx_eq(get_distance((0.0, 0.0), (0.0, 180.0)), 20015.088);
    assert_approx_eq(get_distance((90.0, 0.0), (-90.0, 180.0)), 20015.088);
}
