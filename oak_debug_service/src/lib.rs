//
// Copyright 2024 The Project Oak Authors
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
pub mod proto {
    pub mod oak {
        pub mod debug {
            tonic::include_proto!("oak.debug");
        }
    }
    pub mod perftools {
        pub mod profiles {
            tonic::include_proto!("perftools.profiles");
        }
    }
}
use std::time::Duration;

use pprof::protos::Message as _;
use proto::{
    oak::debug::{debug_service_server::DebugServiceServer, CpuProfileRequest, CpuProfileResponse},
    perftools::profiles::Profile,
};

use crate::proto::oak::debug::debug_service_server::DebugService;

// Interrupt frequency, in Hz.
const SAMPLE_FREQUENCY: i32 = 100;

pub struct Service {}

impl Service {
    pub fn new_server() -> DebugServiceServer<Self> {
        DebugServiceServer::new(Self {})
    }
}

#[tonic::async_trait]
impl DebugService for Service {
    async fn cpu_profile(
        &self,
        request: tonic::Request<CpuProfileRequest>,
    ) -> tonic::Result<tonic::Response<CpuProfileResponse>> {
        let request = request.into_inner();
        let duration: Duration =
            request.duration.unwrap_or_default().try_into().map_err(|err| {
                tonic::Status::invalid_argument(format!("could not parse given duration: {}", err))
            })?;

        let profile = {
            let guard = pprof::ProfilerGuardBuilder::default()
                .frequency(SAMPLE_FREQUENCY)
                .build()
                .map_err(|err| {
                    tonic::Status::internal(format!("failed to initialize profiler: {}", err))
                })?;
            tokio::time::sleep(duration).await;
            let report = guard.report().build().map_err(|err| {
                tonic::Status::internal(format!("failed to build report: {}", err))
            })?;
            report.pprof().map_err(|err| {
                tonic::Status::internal(format!(
                    "failed to translate report into pprof format: {}",
                    err
                ))
            })?
        };

        // This is silly, but becauce of differing versions of Prost we have to
        // serialize and deserialize the profile protobuf, although they are
        // quite literally the same protobuf under the hood.
        let encoded = profile.encode_to_vec();
        let profile = Profile::decode(&encoded[..]).map_err(|err| {
            tonic::Status::internal(format!("failed to deserialize profile proto: {}", err))
        })?;

        Ok(tonic::Response::new(CpuProfileResponse { profile: Some(profile) }))
    }
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn profile_test() {
        let svc = Service {};

        let (resp, _) = tokio::join!(
            svc.cpu_profile(tonic::Request::new(CpuProfileRequest {
                duration: Some(Duration::from_secs(5).try_into().unwrap()),
            })),
            async {
                // Burn some CPU doing something for the profiler to catch by computing some
                // fake Fibonacci.
                let mut fib: Vec<u64> = Vec::with_capacity(1_000_000);
                fib.push(0u64);
                fib.push(1);
                for i in 2..fib.capacity() {
                    fib.push(fib[i - 1].wrapping_add(fib[i - 2]));
                }
            }
        );
        let resp = resp.unwrap().into_inner();

        // What _exactly_ is in the profile is highly variable, but we should have
        // _something_ in there.
        assert!(!resp.profile.unwrap().sample.is_empty());
    }
}
