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

use crate::logger::Logger;
use anyhow::Context;
use futures::future::FutureExt;
use oak_functions_abi::{proto::ServerPolicy, Response, StatusCode};
use serde::Deserialize;
use std::{convert::TryInto, str, time::Duration};

// TODO(#2776): Refactor and move the type alias somewhere more appropriate.
pub type WasmHandler = oak_functions_wasm::WasmHandler<Logger>;

/// Minimum size of constant response bytes. It is large enough to fit an error response, in case
/// the policy is violated.
const MIN_RESPONSE_SIZE: u32 = 50;

/// Similar to [`ServerPolicy`], but it is used for reading the policy provided in the config,
/// and is therefore not guaranteed to be valid.
#[derive(Deserialize, Debug, Clone, Copy)]
#[serde(deny_unknown_fields)]
pub struct Policy {
    /// See [`Policy::constant_response_size_bytes`]
    pub constant_response_size_bytes: u32,
    /// A fixed response time. See [`ServerPolicy::constant_processing_time_ms`].
    #[serde(with = "humantime_serde")]
    pub constant_processing_time: Duration,
}

impl Policy {
    pub fn validate(&self) -> anyhow::Result<ServerPolicy> {
        anyhow::ensure!(
            self.constant_response_size_bytes >= MIN_RESPONSE_SIZE,
            "Response size is too small",
        );

        Ok(ServerPolicy {
            constant_response_size_bytes: self.constant_response_size_bytes,
            constant_processing_time_ms: self
                .constant_processing_time
                .as_millis()
                .try_into()
                .context("could not convert milliseconds to u32")?,
        })
    }
}

/// Trait with a single function for padding the body of an object so that it could be serialized
/// into a byte array of a fixed size.
trait FixedSizeBodyPadder {
    /// Adds padding to the body of this instance to make the size of the body equal to `body_size`.
    fn pad(&self, body_size: usize) -> anyhow::Result<Self>
    where
        Self: std::marker::Sized;
}

impl FixedSizeBodyPadder for Response {
    /// Creates and returns a new [`Response`] instance with the same `status` and `body` as `self`,
    /// except that the `body` may be padded, by adding a number trailing 0s, to make its length
    /// equal to `body_size`. Sets the `length` of the new instance to the length of `self.body`.
    /// Returns an error if the length of the `body` is larger than `body_size`.
    fn pad(&self, body_size: usize) -> anyhow::Result<Self> {
        if self.body.len() <= body_size {
            let mut body = self.body.as_slice().to_vec();
            // Set the length to the actual length of the body before padding.
            let length = body.len() as u64;
            // Add trailing 0s
            body.resize(body_size, 0);
            Ok(Response {
                status: self.status,
                body,
                length,
            })
        } else {
            anyhow::bail!("response body is larger than the input body_size")
        }
    }
}

/// Runs the given function and applies the given security policy to the execution of the function
/// and the response returned from it. Serializes and returns the response as a binary
/// protobuf-encoded byte array of a constant size.
///
/// If the execution of the `function` takes longer than allowed by the given security policy,
/// an error response with status `PolicyTimeViolation` is returned. If the size of the `body` in
/// the response returned by the `function` is larger than allowed by the security policy, the
/// response is discarded and a response with status `PolicySizeViolation` is returned instead.
/// In all cases, to keep the total size of the returned byte array constant, the `body` of the
/// response may be padded by a number of trailing 0s before encoding the response as a binary
/// protobuf message. In this case, the `length` in the response will contain the effective length
/// of the `body`. This response is guaranteed to comply with the policy's size restriction.
pub async fn apply_policy<F>(policy: ServerPolicy, function: F) -> anyhow::Result<Response>
where
    F: std::marker::Send + 'static + FnOnce() -> anyhow::Result<Response>,
{
    // Use tokio::spawn to actually run the tasks in parallel, for more accurate measurement
    // of time.
    let sleep = tokio::spawn(tokio::time::sleep(Duration::from_millis(
        policy.constant_processing_time_ms.into(),
    )));
    let task = tokio::task::spawn_blocking(function);

    // Sleep until the policy times out
    sleep.await?;

    // Get the result whether the task has finnished or not.
    let function_response = task.now_or_never();

    let response = match function_response {
        // The `function` did not terminate within the policy timeout
        None => Response::create(
            StatusCode::PolicyTimeViolation,
            "Reason: response not available.".as_bytes().to_vec(),
        ),
        Some(response) => match response {
            // `tokio::task::JoinError` when getting the response from the tokio task
            Err(_tokio_err) => Response::create(
                StatusCode::InternalServerError,
                "Reason: internal server error.".as_bytes().to_vec(),
            ),
            Ok(response) => match response {
                // The `function` terminated with an error
                Err(err) => Response::create(
                    StatusCode::InternalServerError,
                    err.to_string().as_bytes().to_vec(),
                ),
                Ok(rsp) => rsp,
            },
        },
    };

    // Return an error response if the body of the response is larger than allowed by the policy.
    let response = if response.body.len() > policy.constant_response_size_bytes as usize {
        Response::create(
            StatusCode::PolicySizeViolation,
            "Reason: the response is too large.".as_bytes().to_vec(),
        )
    } else {
        response
    };
    response.pad(
        policy
            .constant_response_size_bytes
            .try_into()
            .context("could not convert u64 to usize")?,
    )
}
