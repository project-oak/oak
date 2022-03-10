//
// Copyright 2022 The Project Oak Authors
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

pub mod demux;
pub mod io;
pub mod log;
pub mod lookup;
pub mod policy;
pub mod wasmi;

use maplit::btreemap;
use std::{collections::BTreeMap, sync::Arc};

/// Manages the shared state for a service.
pub trait Service {
    /// Creates a new service proxy
    fn create_proxy(&self) -> Box<dyn ServiceProxy>;

    /// Configures the servcice with the given data.
    ///
    /// Each service is responsible for interpreting the bytes approriately.
    ///
    /// Most services should only react to receiving configuration data once, except for the lookup
    /// service which will periodically receive lookup data refreshes through this interface.
    fn configure(&self, data: &[u8]) -> anyhow::Result<()>;
}

/// Provides per-request processing with access to the service.
pub trait ServiceProxy {
    /// Processes the provided data, potentially calling other service proxies and returns the
    /// result.
    fn call(&self, data: &[u8]) -> anyhow::Result<Vec<u8>>;
}

/// The types of services we can support.
#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord)]
pub enum ServiceType {
    Log,
    Lookup,
    Policy,
    Session,
    Wasm,
}

fn main() -> anyhow::Result<()> {
    // Create the log service.
    let log: Arc<Box<dyn Service>> = Arc::new(Box::new(log::LogService::new()));
    // Create the lookup service.
    let lookup: Arc<Box<dyn Service>> = Arc::new(Box::new(lookup::LookupService::new()));

    // Create Wasm sandbox service with references to services it can use.
    let services: BTreeMap<ServiceType, Arc<Box<dyn Service>>> = btreemap! {
        ServiceType::Log => log,
        ServiceType::Lookup => lookup,
    };
    let wasm: Arc<Box<dyn Service>> = Arc::new(Box::new(wasmi::WasmiService::new(services)));

    // Create the policy enforcment service that forwards data to the Wasm sandbox service.
    let policy: Arc<Box<dyn Service>> = Arc::new(Box::new(policy::PolicyService::new(wasm)));

    // Create the stream demultiplexer and configure it to send data via the policy enforcement
    // service.
    let demux = demux::Demux::new(policy);

    // Create the fake IO listener and pretend to lister for incoming frames.
    let io = io::IoListener::new(demux);
    io.listen()
}
