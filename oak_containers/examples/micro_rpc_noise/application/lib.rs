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

/// A trivial "application handler" for our demo.
/// Right now the application only handles one request type, which accepts bytes
/// as input.
///
/// We can evolve this to be a more interesting example.
pub fn handle(request_bytes: &[u8]) -> anyhow::Result<Vec<u8>> {
    let name = String::from_utf8_lossy(request_bytes);
    Ok(format!("Hello from application, {name}!",).into_bytes())
}
