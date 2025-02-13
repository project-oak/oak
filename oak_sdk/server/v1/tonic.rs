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

use std::{pin::Pin, sync::Arc};

use oak_proto_rust::oak::session::v1::{RequestWrapper, ResponseWrapper};
use tokio_stream::{Stream, StreamExt};

use crate::oak_application_context::OakApplicationContext;

/// Helper for handling streaming requests presented by a tonic server
/// implementation.

pub type OakApplicationStream =
    Pin<Box<dyn Stream<Item = Result<ResponseWrapper, tonic::Status>> + Send + 'static>>;

pub async fn oak_application(
    application_context: Arc<OakApplicationContext>,
    request: tonic::Request<tonic::Streaming<RequestWrapper>>,
) -> Result<tonic::Response<OakApplicationStream>, tonic::Status> {
    let mut request_stream = request.into_inner();

    let response_stream = async_stream::try_stream! {
        while let Some(request) = request_stream.next().await {
            let request_wrapper = request
                .map_err(|e| tonic::Status::internal(format!("failed to read request from stream: {e:?}")))?;

            yield application_context
                .handle_request(&request_wrapper)
                .await
                .map_err(|e| tonic::Status::internal(format!("failed to handle request: {e:?}")))?;
        }
    };

    Ok(tonic::Response::new(Box::pin(response_stream) as OakApplicationStream))
}
