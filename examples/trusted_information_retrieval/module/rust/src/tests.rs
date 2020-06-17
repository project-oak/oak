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

use crate::{proto::Location, TrustedInformationRetrievalNode};

fn distance(first: (f32, f32), second: (f32, f32)) -> f32 {
    TrustedInformationRetrievalNode::distance(
        Location {
            latitude: first.0,
            longitude: first.1,
        },
        Location {
            latitude: second.0,
            longitude: second.1,
        },
    )
}

#[test]
fn test_distance() {
    assert_approx_eq(distance((0.0, 0.0), (0.0, 0.0)), 0.0);
    assert_approx_eq(distance((0.0, 0.0), (10.0, 10.0)), 1568.5204);
    assert_approx_eq(distance((10.0, 10.0), (-10.0, -10.0)), 3137.0413);
    assert_approx_eq(distance((0.0, 0.0), (0.0, 180.0)), 20015.088);
    assert_approx_eq(distance((90.0, 0.0), (-90.0, 180.0)), 20015.088);
}

fn assert_approx_eq(left: f32, right: f32) {
    if (left - right).abs() > 0.01 {
        panic!("{} is not equal to {}", left, right);
    }
}
