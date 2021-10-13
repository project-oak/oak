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

use tonic::{service::interceptor::Interceptor, Request, Status};

#[cfg(test)]
mod tests;

pub mod auth;
pub mod label;

/// This struct is created by the [`combine`] method. See its documentation for more.
#[derive(Clone)]
pub struct CombinedInterceptor<A: Interceptor, B: Interceptor> {
    interceptor_a: A,
    interceptor_b: B,
}

/// Combines the two provided interceptor, executing the first one, and if that succeeds then also
/// the second one, sequentially. If the first one returns an Error response, the second one is
/// never executed.
pub fn combine<A: Interceptor, B: Interceptor>(
    interceptor_a: A,
    interceptor_b: B,
) -> CombinedInterceptor<A, B> {
    CombinedInterceptor {
        interceptor_a,
        interceptor_b,
    }
}

impl<A: Interceptor, B: Interceptor> Interceptor for CombinedInterceptor<A, B> {
    fn call(&mut self, request: Request<()>) -> Result<Request<()>, Status> {
        let request = self.interceptor_a.call(request)?;
        self.interceptor_b.call(request)
    }
}
