//
// Copyright 2021 The Project Oak Authors
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

//! Extension to support testing.

use chrono::{SecondsFormat, Utc};
use oak_functions_abi::{proto::OakStatus, ExtensionHandle, TestingRequest, TestingResponse};
use oak_functions_extension::{ExtensionFactory, OakApiNativeExtension};
use oak_logger::{Level, OakLogger};

impl<L> OakApiNativeExtension for TestingExtension<L>
where
    L: OakLogger,
{
    fn invoke(&mut self, request: Vec<u8>) -> Result<Vec<u8>, OakStatus> {
        let request =
            bincode::deserialize(&request).expect("failed to deserialize testing request");

        let response = match request {
            TestingRequest::Echo(echo_message) => {
                let echo_response = TestingResponse::Echo(echo_message);
                bincode::serialize(&echo_response).expect("failed to serialize testing request")
            }
            TestingRequest::Blackhole(message) => {
                self.logger.log_sensitive(Level::Debug, &message);
                // We don't expect the BlackholeRequest to give back a result.
                Vec::new()
            }
        };
        Ok(response)
    }

    fn terminate(&mut self) -> anyhow::Result<()> {
        Ok(())
    }

    fn get_handle(&self) -> ExtensionHandle {
        ExtensionHandle::TestingHandle
    }
}
pub struct TestingFactory<L: OakLogger> {
    logger: L,
}

impl<L> TestingFactory<L>
where
    L: OakLogger + 'static,
{
    pub fn new_boxed_extension_factory(logger: L) -> anyhow::Result<Box<dyn ExtensionFactory<L>>> {
        Ok(Box::new(Self { logger }))
    }
}

impl<L> ExtensionFactory<L> for TestingFactory<L>
where
    L: OakLogger + 'static,
{
    fn create(&self) -> anyhow::Result<Box<dyn OakApiNativeExtension>> {
        let extension = TestingExtension::new(self.logger.clone());
        Ok(Box::new(extension))
    }
}
struct TestingExtension<L: OakLogger> {
    logger: L,
}

impl<L> TestingExtension<L>
where
    L: OakLogger,
{
    pub fn new(logger: L) -> Self {
        Self { logger }
    }
}

/// Implemenation of the `oak_loggger::OakLogger` trait to support testing with the `TestExtension`
/// without needing a reference to the implementation in the Oak Functions Loader.
#[derive(Clone)]
pub struct TestingLogger {}

// TODO(#2417): Implement a testing logger that collects all messages. See also #2783.
impl TestingLogger {
    pub fn for_test() -> Self {
        Self {}
    }

    fn log(&self, message: &str) {
        eprintln!(
            "{} TEST - {}",
            Utc::now().to_rfc3339_opts(SecondsFormat::Secs, true),
            message,
        );
    }
}

impl OakLogger for TestingLogger {
    fn log_sensitive(&self, _level: Level, message: &str) {
        self.log(message);
    }

    fn log_public(&self, _level: Level, message: &str) {
        self.log(message);
    }
}
