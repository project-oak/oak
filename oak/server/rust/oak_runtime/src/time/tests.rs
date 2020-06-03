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

use super::*;
use crate::runtime::tests::init_logging;
use std::time::SystemTime;

// Implements PartialEq to simplify testing assertions.
impl PartialEq for RoughtimeError {
    fn eq(&self, other: &Self) -> bool {
        match self {
            RoughtimeError::NotEnoughOverlappingIntervals { actual, expected } => match other {
                RoughtimeError::NotEnoughOverlappingIntervals {
                    actual: other_actual,
                    expected: other_expected,
                } => actual == other_actual && expected == other_expected,
                _ => false,
            },
            _ => false,
        }
    }
}

#[test]
fn test_valid_overlap_one_of_three() {
    let client = RoughtimeClient::new(vec![], 1, 0, 0, 0);
    let intervals = vec![
        Interval { min: 1, max: 4 },
        Interval { min: 2, max: 6 },
        Interval { min: 3, max: 5 },
    ];
    let result = client.find_overlap(&intervals);
    assert_eq!(Ok(Interval { min: 1, max: 4 }), result);
}

#[test]
fn test_valid_overlap_two_of_three() {
    let client = RoughtimeClient::new(vec![], 2, 0, 0, 0);
    let intervals = vec![
        Interval { min: 1, max: 4 },
        Interval { min: 2, max: 6 },
        Interval { min: 3, max: 5 },
    ];
    let result = client.find_overlap(&intervals);
    assert_eq!(Ok(Interval { min: 2, max: 4 }), result);
}

#[test]
fn test_valid_overlap_three_of_three() {
    let client = RoughtimeClient::new(vec![], 3, 0, 0, 0);
    let intervals = vec![
        Interval { min: 1, max: 4 },
        Interval { min: 2, max: 6 },
        Interval { min: 3, max: 5 },
    ];
    let result = client.find_overlap(&intervals);
    assert_eq!(Ok(Interval { min: 3, max: 4 }), result);
}

#[test]
fn test_valid_overlap_one_of_three_reversed() {
    let client = RoughtimeClient::new(vec![], 1, 0, 0, 0);
    let intervals = vec![
        Interval { min: 3, max: 5 },
        Interval { min: 2, max: 6 },
        Interval { min: 1, max: 4 },
    ];
    let result = client.find_overlap(&intervals);
    assert_eq!(Ok(Interval { min: 3, max: 5 }), result);
}

#[test]
fn test_valid_overlap_two_of_three_reversed() {
    let client = RoughtimeClient::new(vec![], 2, 0, 0, 0);
    let intervals = vec![
        Interval { min: 3, max: 5 },
        Interval { min: 2, max: 6 },
        Interval { min: 1, max: 4 },
    ];
    let result = client.find_overlap(&intervals);
    assert_eq!(Ok(Interval { min: 3, max: 5 }), result);
}

#[test]
fn test_valid_overlap_three_of_three_reversed() {
    let client = RoughtimeClient::new(vec![], 3, 0, 0, 0);
    let intervals = vec![
        Interval { min: 3, max: 5 },
        Interval { min: 2, max: 6 },
        Interval { min: 1, max: 4 },
    ];
    let result = client.find_overlap(&intervals);
    assert_eq!(Ok(Interval { min: 3, max: 4 }), result);
}

#[test]
fn test_valid_overlap_five_of_ten() {
    let client = RoughtimeClient::new(vec![], 5, 0, 0, 0);
    let intervals = vec![
        Interval { min: 1, max: 2 },
        Interval { min: 1, max: 9 },
        Interval { min: 2, max: 9 },
        Interval { min: 3, max: 9 },
        Interval { min: 4, max: 9 },
        Interval { min: 5, max: 9 },
        Interval { min: 6, max: 9 },
        Interval { min: 7, max: 9 },
        Interval { min: 8, max: 9 },
        Interval { min: 9, max: 9 },
    ];
    let result = client.find_overlap(&intervals);
    assert_eq!(Ok(Interval { min: 5, max: 9 }), result);
}

#[test]
fn test_valid_overlap_point() {
    let client = RoughtimeClient::new(vec![], 2, 0, 0, 0);
    let intervals = vec![Interval { min: 4, max: 8 }, Interval { min: 1, max: 4 }];
    let result = client.find_overlap(&intervals);
    assert_eq!(Ok(Interval { min: 4, max: 4 }), result);
}

#[test]
fn test_invalid_overlap_four_of_three() {
    let client = RoughtimeClient::new(vec![], 4, 0, 0, 0);
    let intervals = vec![
        Interval { min: 1, max: 4 },
        Interval { min: 2, max: 6 },
        Interval { min: 3, max: 5 },
    ];
    let result = client.find_overlap(&intervals);
    assert_eq!(
        Err(RoughtimeError::NotEnoughOverlappingIntervals {
            actual: 3,
            expected: 4
        }),
        result
    );
}

#[test]
fn test_invalid_overlap_three_of_three() {
    let client = RoughtimeClient::new(vec![], 3, 0, 0, 0);
    let intervals = vec![
        Interval { min: 1, max: 2 },
        Interval { min: 3, max: 6 },
        Interval { min: 3, max: 5 },
    ];
    let result = client.find_overlap(&intervals);
    assert_eq!(
        Err(RoughtimeError::NotEnoughOverlappingIntervals {
            actual: 2,
            expected: 3
        }),
        result
    );
}

#[test]
fn test_invalid_overlap_inverted_intervals() {
    let client = RoughtimeClient::new(vec![], 3, 0, 0, 0);
    let intervals = vec![
        Interval { min: 4, max: 1 },
        Interval { min: 6, max: 2 },
        Interval { min: 5, max: 3 },
    ];
    let result = client.find_overlap(&intervals);
    assert_eq!(
        Err(RoughtimeError::NotEnoughOverlappingIntervals {
            actual: 0,
            expected: 3
        }),
        result
    );
}

#[test]
#[ignore]
/// Gets Roughtime from the live default servers with the default settings.
///
/// This requires an internet connection and at least 3 of the default servers to be operational and
/// accessible.
fn test_get_roughtime_live() {
    init_logging();
    let client = RoughtimeClient::default();
    let roughtime: u128 = client.get_roughtime().unwrap().into();
    let current = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap()
        .as_micros();

    assert!(
        roughtime.saturating_sub(DEFAULT_MAX_RADIUS_MICROSECONDS.into()) <= current
            && roughtime.saturating_add(DEFAULT_MAX_RADIUS_MICROSECONDS.into()) >= current
    );
}
