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

use micro_rpc::Transport;

// pub trait Transport { 
//     /// Type representing any transport-specific errors. By default, the transport is assumed to be 
//     /// infallible. 
//     type Error = !; 
//     fn invoke(&mut self, request_bytes: &[u8]) -> Result<Vec<u8>, Self::Error>; 
// } 

pub struct GrpcTransport {
    rpc_client: StreamingSessionClient<Channel>,
}

impl GrpcTransport {
    pub fn new(rpc_client: StreamingSessionClient<Channel>) -> Self {
        Self { rpc_client }
    }
}

impl Transport for GrpcTransport {
    type Error = u32;

    fn invoke(&mut self, request_bytes: &[u8]) -> anyhow::Result<Vec<u8>> {
        let invoke_request = InvokeRequest {
            encrypted_body: body.to_vec(),
        };
        let mut response_stream = self
            .rpc_client(futures_util::stream::iter(vec![RequestWrapper {
                request: Some(request_wrapper::Request::InvokeRequest(invoke_request)),
            }]))
            .await
            .context("couldn't send message")?
            .into_inner();
        // Read the next (and only) message from the response stream.
        let response_wrapper = response_stream
            .message()
            .await
            .context("gRPC server error when invoking method")?
            .context("received empty response stream")?;

        let Some(response_wrapper::Response::InvokeResponse(invoke_response)) = response_wrapper.response  else {
            return Err(anyhow::anyhow!("response_wrapper does not have a valid invoke_response message"))
        };

        Ok(invoke_response.encrypted_body)
    }
}




