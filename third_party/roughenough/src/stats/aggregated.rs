// Copyright 2017-2019 int08h LLC
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

use std::net::IpAddr;
use std::collections::HashMap;
use std::collections::hash_map::Iter;

use crate::stats::ClientStatEntry;
use crate::stats::ServerStats;

///
/// Implementation of `ServerStats` that provides high-level aggregated client statistics. No
/// per-client statistic are maintained and runtime memory use is constant.
///
#[allow(dead_code)]
pub struct AggregatedStats {
    valid_requests: u64,
    invalid_requests: u64,
    health_checks: u64,
    responses_sent: u64,
    bytes_sent: usize,
    empty_map: HashMap<IpAddr, ClientStatEntry>,
}

impl Default for AggregatedStats {
    fn default() -> Self {
        Self::new()
    }
}

impl AggregatedStats {

    #[allow(dead_code)]
    pub fn new() -> Self {
        AggregatedStats {
            valid_requests: 0,
            invalid_requests: 0,
            health_checks: 0,
            responses_sent: 0,
            bytes_sent: 0,
            empty_map: HashMap::new()
        }
    }
}

impl ServerStats for AggregatedStats {
    fn add_valid_request(&mut self, _: &IpAddr) {
        self.valid_requests += 1
    }

    fn add_invalid_request(&mut self, _: &IpAddr) {
        self.invalid_requests += 1
    }

    fn add_health_check(&mut self, _: &IpAddr) {
        self.health_checks += 1
    }

    fn add_response(&mut self, _: &IpAddr, bytes_sent: usize) {
        self.bytes_sent += bytes_sent;
        self.responses_sent += 1;
    }

    fn total_valid_requests(&self) -> u64 {
        self.valid_requests
    }

    fn total_invalid_requests(&self) -> u64 {
        self.invalid_requests
    }

    fn total_health_checks(&self) -> u64 {
        self.health_checks
    }

    fn total_responses_sent(&self) -> u64 {
        self.responses_sent
    }

    fn total_bytes_sent(&self) -> usize {
        self.bytes_sent
    }

    fn total_unique_clients(&self) -> u64 {
        0
    }

    fn stats_for_client(&self, _addr: &IpAddr) -> Option<&ClientStatEntry> {
        None
    }

    fn iter(&self) -> Iter<IpAddr, ClientStatEntry> {
        self.empty_map.iter()
    }

    fn clear(&mut self) {}
}
