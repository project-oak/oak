//
// Copyright 2025 The Project Oak Authors
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

use prost_types::Timestamp;

/// Converts UNIX milliseconds since epoch point into the Timestamp proto.
pub fn to_timestamp(milliseconds_since_epoch: i64) -> Timestamp {
    let seconds = milliseconds_since_epoch / 1000;
    let nanos = (milliseconds_since_epoch % 1000 * 1_000_000) as i32;
    Timestamp { seconds, nanos }
}

/// Converts Timestamp proto to UNIX milliseconds since epoch.
pub fn to_milliseconds_since_epoch(timestamp: &Timestamp) -> i64 {
    timestamp.seconds * 1000 + (timestamp.nanos / 1_000_000) as i64
}

#[cfg(test)]
mod tests {
    use prost_types::Timestamp;

    use crate::certificate::utils::{to_milliseconds_since_epoch, to_timestamp};

    #[test]
    fn test_to_timestamp() {
        let milliseconds = 10_000;
        let expected_timestamp = Timestamp { seconds: 10, nanos: 0 };
        assert_eq!(to_timestamp(milliseconds), expected_timestamp);
    }

    #[test]
    fn test_to_timestamp_with_nanos() {
        let milliseconds = 12_345;
        let expected_timestamp = Timestamp { seconds: 12, nanos: 345_000_000 };
        assert_eq!(to_timestamp(milliseconds), expected_timestamp);
    }

    #[test]
    fn test_from_timestamp() {
        let timestamp = Timestamp { seconds: 0, nanos: 123_456_789 };
        assert_eq!(to_milliseconds_since_epoch(&timestamp), 123);
    }

    #[test]
    fn test_from_timestamp_with_nanos() {
        let timestamp = Timestamp { seconds: 1_700_000_000, nanos: 987_654_321 };
        assert_eq!(to_milliseconds_since_epoch(&timestamp), 1_700_000_000_987);
    }

    #[test]
    fn test_to_from_timestamp() {
        let expected_milliseconds = 12_345;
        let timestamp = to_timestamp(expected_milliseconds);
        let milliseconds = to_milliseconds_since_epoch(&timestamp);
        assert_eq!(milliseconds, expected_milliseconds);
    }
}
