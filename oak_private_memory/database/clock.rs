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

use std::time::SystemTime;

/// A trait for providing the current time.
pub trait Clock: Send + Sync {
    fn now(&self) -> SystemTime;
}

/// Converts SystemTime to prost_types::Timestamp.
pub fn system_time_to_timestamp(system_time: SystemTime) -> prost_types::Timestamp {
    let (seconds, nanos) = match system_time.duration_since(SystemTime::UNIX_EPOCH) {
        Ok(duration) => {
            let seconds = duration.as_secs() as i64;
            let nanos = duration.subsec_nanos() as i32;
            (seconds, nanos)
        }
        Err(e) => {
            let duration = e.duration();
            let seconds = -(duration.as_secs() as i64);
            let nanos = -(duration.subsec_nanos() as i32);
            (seconds, nanos)
        }
    };

    prost_types::Timestamp { seconds, nanos }
}

/// A clock that uses the system time.
pub struct SystemClock;

impl Clock for SystemClock {
    fn now(&self) -> SystemTime {
        SystemTime::now()
    }
}
