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

use futures::future::join_all;
use log::warn;
use roughenough::{
    client::{create_nonce, make_request, ParsedResponse, ResponseHandler},
    RtMessage,
};
use std::net::{SocketAddr, ToSocketAddrs as _};
use tokio::{net::UdpSocket, runtime::Runtime};

#[cfg(test)]
mod tests;

const DEFAULT_MIN_OVERLAPPING_INTERVALS: usize = 3;
const DEFAULT_MAX_RADIUS_MICROSECONDS: u32 = 60000000;
const MAX_RESPONSE_SIZE: usize = 1024;

/// Specifies the details of a Roughtime server.
///
/// Only UDP is supported as a protocol and ED25519 as a public key type.
pub struct RoughtimeServerSpec {
    /// The name of the Roughtime server.
    name: String,
    /// The address of the Roughtime server.
    host: String,
    /// The port on which the Roughtime server is listening.
    port: u16,
    /// The base64-encoded public key for the Roughtime server.
    public_key_base64: String,
}

/// A client for requesting Roughtime from multiple servers.
///
/// Time is given as microseconds since the UNIX epoch (00:00:00 UTC on 1 January 1970).
/// Leap seconds are linearly smeared over a 24-hour period. That is, the smear extends from
/// UTC noon to noon over 86,401 or 86,399 SI seconds, and all the smeared seconds are the same
/// length.
pub struct RoughtimeClient {
    /// The list of Roughtime servers to use.
    servers: Vec<RoughtimeServerSpec>,
    /// The minimum number of intervals from different servers that must overlap for the response
    /// to be considered valid.
    min_overlapping_intervals: usize,
    /// The maximum radius returned by any server for the response to still be acceptable.
    max_radius_microseconds: u32,
}

impl RoughtimeClient {
    /// Creates a new Roughtime client with the default settings.
    pub fn default() -> Self {
        RoughtimeClient {
            servers: get_default_servers(),
            min_overlapping_intervals: DEFAULT_MIN_OVERLAPPING_INTERVALS,
            max_radius_microseconds: DEFAULT_MAX_RADIUS_MICROSECONDS,
        }
    }

    /// Creates a new Roughtime client.
    pub fn new(
        servers: Vec<RoughtimeServerSpec>,
        min_overlapping_intervals: usize,
        max_radius_microseconds: u32,
    ) -> Self {
        RoughtimeClient {
            servers,
            min_overlapping_intervals,
            max_radius_microseconds,
        }
    }

    /// Gets the Roughtime from multiple servers.
    ///
    /// It is calculated as the midpoint of the first `min_overlapping_intervals` overlap between
    /// the intervals returned from the servers.
    pub fn get_roughtime(&self) -> Result<u64, RoughtimeError> {
        let mut runtime = Runtime::new()?;
        let intervals = runtime.block_on(self.get_intervals_from_all_servers());
        let result = self.find_overlap(&intervals)?;
        Ok((result.min + result.max) / 2)
    }

    /// Gets the Roughtime intervals from each of the servers.
    async fn get_intervals_from_all_servers(&self) -> Vec<Interval> {
        let mut pending = Vec::new();
        for server in &self.servers {
            pending.push(self.get_interval_from_server(server));
        }

        join_all(pending)
            .await
            .iter()
            .filter_map(|interval| interval.clone())
            .collect()
    }

    /// Finds the interval that represents the overlap of the first `min_overlapping_intervals`
    /// overlapping intervals.
    fn find_overlap(&self, intervals: &Vec<Interval>) -> Result<Interval, RoughtimeError> {
        let mut max_count = 0;
        for interval in intervals {
            let mut count = 0;
            let mut min = 0;
            let mut max = u64::MAX;
            let point = interval.min;
            for test in intervals {
                if point >= test.min && point <= test.max {
                    if test.min > min {
                        min = test.min;
                    }
                    if test.max < max {
                        max = test.max;
                    }
                    count += 1;
                    if count == self.min_overlapping_intervals {
                        return Ok(Interval { min, max });
                    }
                }
            }
            if count > max_count {
                max_count = count;
            }
        }

        Err(RoughtimeError::NotEnoughOverlappingIntervals {
            actual: max_count,
            expected: self.min_overlapping_intervals,
        })
    }

    /// Gets the Roughtime interval from a single server.
    async fn get_interval_from_server(&self, server: &RoughtimeServerSpec) -> Option<Interval> {
        match self.get_roughtime_from_server(server).await {
            Ok(interval) => Some(interval),
            Err(error) => {
                warn!("Error getting Roughtime from {}: {:?}", &server.name, error);
                None
            }
        }
    }

    /// Makes a Roughtime UDP request to a server.
    async fn get_roughtime_from_server(
        &self,
        server: &RoughtimeServerSpec,
    ) -> Result<Interval, Box<dyn std::error::Error>> {
        let nonce = create_nonce()?;
        let request = make_request(&nonce)?;
        let response = Self::send_roughtime_request(server, &request).await?;
        let ParsedResponse {
            verified,
            midpoint,
            radius,
        } = ResponseHandler::new(
            base64::decode(server.public_key_base64.as_bytes())?,
            RtMessage::from_bytes(response.as_ref())?,
            nonce.to_owned(),
        )?
        .extract_time()?;

        match verified {
            true => match radius {
                radius if radius <= self.max_radius_microseconds => match midpoint {
                    midpoint if midpoint > radius.into() => Ok(Interval {
                        min: midpoint.saturating_sub(radius.into()),
                        max: midpoint.saturating_add(radius.into()),
                    }),
                    _ => Err(RoughtimeError::MidPointTooSmall.into()),
                },
                _ => Err(RoughtimeError::RadiusTooLarge.into()),
            },
            _ => Err(RoughtimeError::InvalidSignature.into()),
        }
    }

    async fn send_roughtime_request(
        server: &RoughtimeServerSpec,
        request: &Vec<u8>,
    ) -> std::io::Result<Vec<u8>> {
        let remote_addr = (&server.host[..], server.port)
            .to_socket_addrs()?
            .next()
            .unwrap();
        let local_address: SocketAddr = if remote_addr.is_ipv4() {
            "0.0.0.0:0"
        } else {
            "[::]:0"
        }
        .parse()
        .unwrap();
        let mut socket = UdpSocket::bind(local_address).await?;
        socket.connect(&remote_addr).await?;
        socket.send(request).await?;
        let mut data = vec![0u8; MAX_RESPONSE_SIZE];
        socket.recv(&mut data).await?;
        Ok(data)
    }
}

/// Gets the default Roughtime servers in the ecosystem.
///
/// Based on
/// https://github.com/cloudflare/roughtime/blob/569dc6f5119970035fe0a008b83398d59363ed45/ecosystem.json
fn get_default_servers() -> Vec<RoughtimeServerSpec> {
    vec![
        RoughtimeServerSpec {
            name: "Caesium".to_owned(),
            host: "caesium.tannerryan.ca".to_owned(),
            port: 2002,
            public_key_base64: "iBVjxg/1j7y1+kQUTBYdTabxCppesU/07D4PMDJk2WA=".to_owned(),
        },
        RoughtimeServerSpec {
            name: "Chainpoint-Roughtime".to_owned(),
            host: "roughtime.chainpoint.org".to_owned(),
            port: 2002,
            public_key_base64: "bbT+RPS7zKX6w71ssPibzmwWqU9ffRV5oj2OresSmhE=".to_owned(),
        },
        RoughtimeServerSpec {
            name: "Cloudflare-Roughtime".to_owned(),
            host: "roughtime.cloudflare.com".to_owned(),
            port: 2002,
            public_key_base64: "gD63hSj3ScS+wuOeGrubXlq35N1c5Lby/S+T7MNTjxo=".to_owned(),
        },
        RoughtimeServerSpec {
            name: "Google-Sandbox-Roughtime".to_owned(),
            host: "roughtime.sandbox.google.com".to_owned(),
            port: 2002,
            public_key_base64: "etPaaIxcBMY1oUeGpwvPMCJMwlRVNxv51KK/tktoJTQ=".to_owned(),
        },
        RoughtimeServerSpec {
            name: "int08h-Roughtime".to_owned(),
            host: "roughtime.int08h.com".to_owned(),
            port: 2002,
            public_key_base64: "AW5uAoTSTDfG5NfY1bTh08GUnOqlRb+HVhbJ3ODJvsE=".to_owned(),
        },
        RoughtimeServerSpec {
            name: "ticktock".to_owned(),
            host: "ticktock.mixmin.net".to_owned(),
            port: 5333,
            public_key_base64: "cj8GsiNlRkqiDElAeNMSBBMwrAl15hYPgX50+GWX/lA=".to_owned(),
        },
    ]
}

/// Possible errors returned by the Roughtime client.
#[derive(Debug)]
pub enum RoughtimeError {
    InvalidSignature,
    IoError(tokio::io::Error),
    MidPointTooSmall,
    NotEnoughOverlappingIntervals { actual: usize, expected: usize },
    RadiusTooLarge,
}

impl std::fmt::Display for RoughtimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RoughtimeError::InvalidSignature => write!(f, "Could not verify signature."),
            RoughtimeError::IoError(e) => write!(f, "I/O error: {}", e),
            RoughtimeError::MidPointTooSmall => write!(f, "Midpoint too small."),
            RoughtimeError::NotEnoughOverlappingIntervals { actual, expected } => write!(
                f,
                "Required {} overlapping intervals, but only found {}.",
                expected, actual
            ),
            RoughtimeError::RadiusTooLarge => write!(f, "Radius too large."),
        }
    }
}

impl std::error::Error for RoughtimeError {}

impl From<tokio::io::Error> for RoughtimeError {
    fn from(err: tokio::io::Error) -> Self {
        RoughtimeError::IoError(err)
    }
}

/// A time interval.
///
/// Both `min` and `max` are interpreted as microseconds since the UNIX epoch.
#[derive(Clone)]
struct Interval {
    min: u64,
    max: u64,
}
