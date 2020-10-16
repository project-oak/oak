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

pub mod native;
pub mod oak;

use async_trait::async_trait;

#[async_trait]
pub trait ApplicationClient: std::marker::Send {
    /// Sends test requests. Returns `()` since the value of the request is not needed for
    /// current benchmark implementation.
    async fn send_request(&mut self, id: &str) -> Result<(), tonic::Status>;
}
