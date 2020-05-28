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

//!
//! Facilities for tracking client requests to the server
//!

mod aggregated;
mod per_client;

use std::net::IpAddr;
use std::collections::hash_map::Iter;

pub use crate::stats::aggregated::AggregatedStats;
pub use crate::stats::per_client::PerClientStats;

///
/// Specific metrics tracked per each client
///
#[derive(Debug, Clone, Copy)]
pub struct ClientStatEntry {
    pub valid_requests: u64,
    pub invalid_requests: u64,
    pub health_checks: u64,
    pub responses_sent: u64,
    pub bytes_sent: usize,
}

impl ClientStatEntry {
    fn new() -> Self {
        ClientStatEntry {
            valid_requests: 0,
            invalid_requests: 0,
            health_checks: 0,
            responses_sent: 0,
            bytes_sent: 0,
        }
    }
}

///
/// Implementations of this trait record client activity
///
pub trait ServerStats {
    fn add_valid_request(&mut self, addr: &IpAddr);

    fn add_invalid_request(&mut self, addr: &IpAddr);

    fn add_health_check(&mut self, addr: &IpAddr);

    fn add_response(&mut self, addr: &IpAddr, bytes_sent: usize);

    fn total_valid_requests(&self) -> u64;

    fn total_invalid_requests(&self) -> u64;

    fn total_health_checks(&self) -> u64;

    fn total_responses_sent(&self) -> u64;

    fn total_bytes_sent(&self) -> usize;

    fn total_unique_clients(&self) -> u64;

    fn stats_for_client(&self, addr: &IpAddr) -> Option<&ClientStatEntry>;

    fn iter(&self) -> Iter<IpAddr, ClientStatEntry>;

    fn clear(&mut self);
}


#[cfg(test)]
mod test {
    use crate::stats::{ServerStats, PerClientStats};
    use std::net::{IpAddr, Ipv4Addr};

    #[test]
    fn simple_stats_starts_empty() {
        let stats = PerClientStats::new();

        assert_eq!(stats.total_valid_requests(), 0);
        assert_eq!(stats.total_invalid_requests(), 0);
        assert_eq!(stats.total_health_checks(), 0);
        assert_eq!(stats.total_responses_sent(), 0);
        assert_eq!(stats.total_bytes_sent(), 0);
        assert_eq!(stats.total_unique_clients(), 0);
        assert_eq!(stats.num_overflows(), 0);
    }

    #[test]
    fn client_requests_are_tracked() {
        let mut stats = PerClientStats::new();

        let ip1 = "127.0.0.1".parse().unwrap();
        let ip2 = "127.0.0.2".parse().unwrap();
        let ip3 = "127.0.0.3".parse().unwrap();

        stats.add_valid_request(&ip1);
        stats.add_valid_request(&ip2);
        stats.add_valid_request(&ip3);
        assert_eq!(stats.total_valid_requests(), 3);

        stats.add_invalid_request(&ip2);
        assert_eq!(stats.total_invalid_requests(), 1);

        stats.add_response(&ip2, 8192);
        assert_eq!(stats.total_bytes_sent(), 8192);

        assert_eq!(stats.total_unique_clients(), 3);
    }

    #[test]
    fn per_client_stats() {
        let mut stats = PerClientStats::new();
        let ip = "127.0.0.3".parse().unwrap();

        stats.add_valid_request(&ip);
        stats.add_response(&ip, 2048);
        stats.add_response(&ip, 1024);

        let entry = stats.stats_for_client(&ip).unwrap();
        assert_eq!(entry.valid_requests, 1);
        assert_eq!(entry.invalid_requests, 0);
        assert_eq!(entry.responses_sent, 2);
        assert_eq!(entry.bytes_sent, 3072);
    }

    #[test]
    fn overflow_max_entries() {
        let mut stats = PerClientStats::with_limit(100);

        for i in 0..201 {
            let ipv4 = Ipv4Addr::from(i as u32);
            let addr = IpAddr::from(ipv4);

            stats.add_valid_request(&addr);
        };

        assert_eq!(stats.total_unique_clients(), 100);
        assert_eq!(stats.num_overflows(), 101);
    }
}


