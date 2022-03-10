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

use crate::{Service, ServiceProxy};

/// Service to provide loggin functionality.
pub struct LogService {
    // Logger instance will be stored here in future.
}

impl LogService {
    pub fn new() -> Self {
        Self {}
    }
}

impl Service for LogService {
    fn create_proxy(&self) -> Box<dyn ServiceProxy> {
        Box::new(LogProxy::new())
    }
    fn configure(&self, _data: &[u8]) -> anyhow::Result<()> {
        eprintln!("log configured");
        // Ignore configuration for now.
        Ok(())
    }
}

impl Default for LogService {
    fn default() -> Self {
        Self::new()
    }
}

/// Provides the per-request logging functionality.
pub struct LogProxy {
    // Logger instance will be stored here in future.
}

impl LogProxy {
    fn new() -> Self {
        Self {}
    }
}

impl ServiceProxy for LogProxy {
    fn call(&self, data: &[u8]) -> anyhow::Result<Vec<u8>> {
        eprintln!("log called");
        // The real implementation will use the logger. For now we just interpret the data as a UTF8
        // string, write to stderr and echo the data base.
        eprintln!("logged: {}", std::str::from_utf8(data)?);
        Ok(data.to_vec())
    }
}
