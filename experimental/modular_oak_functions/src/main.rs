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

extern crate alloc;

pub mod demux;
pub mod io;
pub mod log;
pub mod lookup;
pub mod policy;
pub mod session;
pub mod wasmi;

use alloc::{collections::BTreeMap, sync::Arc};
use maplit::btreemap;

/// Manages the shared state for a service.
pub trait Service {
    /// Creates a new service proxy
    fn create_proxy(self: Arc<Self>) -> Box<dyn ServiceProxy>;

    /// Configures the servcice with the given data.
    ///
    /// Each service is responsible for interpreting the bytes approriately.
    ///
    /// Most services should only react to receiving configuration data once, except for the lookup
    /// service which will periodically receive lookup data refreshes through this interface.
    fn configure(&self, data: &[u8]) -> anyhow::Result<()>;

    /// Processes the provided data and returns the result.
    fn call(&self, data: &[u8]) -> anyhow::Result<Vec<u8>>;
}

/// Provides per-request processing with access to the service.
pub trait ServiceProxy {
    /// Processes the provided data, potentially calling other service proxies and returns the
    /// result.
    fn call(&self, data: &[u8]) -> anyhow::Result<Vec<u8>>;
}

/// The types of services that can be configured.
#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord)]
pub enum ConfigServiceType {
    Log,
    Lookup,
    Policy,
    Session,
    Wasm,
}

/// The types of services that can be called from a workload.
#[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord)]
pub enum WorkloadServiceType {
    Log,
    Lookup,
}

fn main() -> anyhow::Result<()> {
    // Create the log service.
    let log: Arc<dyn Service> = Arc::new(log::LogService::new());

    // Create the lookup service.
    let lookup: Arc<dyn Service> = Arc::new(lookup::LookupService::new());

    // Create Wasm sandbox service with references to the services it can use.
    let services: BTreeMap<WorkloadServiceType, Arc<dyn Service>> = btreemap! {
        WorkloadServiceType::Log => log.clone(),
        WorkloadServiceType::Lookup => lookup.clone(),
    };
    let wasm: Arc<dyn Service> = Arc::new(wasmi::WasmiService::new(services));

    // Create the policy enforcement service that forwards data to the Wasm sandbox service and
    // applies the fixed response-time and fixed response-size policies.
    let policy: Arc<dyn Service> = Arc::new(policy::PolicyService::new(wasm.clone()));

    // Create the session service that handles remote attestation handshakes and session encryption
    // and decryption.
    let session: Arc<dyn Service> = Arc::new(session::SessionService::new(policy.clone()));

    // Create references to services that can be configured.
    let config_services: BTreeMap<ConfigServiceType, Arc<dyn Service>> = btreemap! {
        ConfigServiceType::Log => log,
        ConfigServiceType::Lookup => lookup,
        ConfigServiceType::Policy => policy,
        ConfigServiceType::Session => session.clone(),
        ConfigServiceType::Wasm => wasm,
    };

    // Create the stream demultiplexer and configure it to configure the other services and send
    // data via the session service.
    let demux = demux::Demux::new(config_services, session);

    // Create the fake IO listener and pretend to listen for incoming frames.
    let io = io::IoListener::new(Arc::new(demux));
    io.listen()
}
