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

use oak_channel::client::{ClientChannelHandle, RequestEncoder};

/// Singleton responsible for sending requests, and receiving responses over the underlying
/// communication channel with the baremetal runtime.
pub struct Connector {
    inner: ClientChannelHandle,
    request_encoder: RequestEncoder,
}

impl Connector {
    /// Spawn an instance of the [`Connector`] in a seperate task, and return a
    /// cloneable [`ConnectorHandle`] for it.
    pub fn spawn(inner: Box<dyn oak_channel::Channel>) -> ConnectorHandle {
        // A message based communication channel that permits other parts of the
        // untrusted launcher to send requests to the task that handles communicating
        // with the runtime and receive responses.
        let (request_dispatcher, mut request_receiver) =
            bmrng::unbounded_channel::<Vec<u8>, Result<Vec<u8>, micro_rpc::Status>>();

        // Spawn task to handle communicating with the runtime and receiving responses.
        tokio::spawn(async move {
            let mut connector = Self {
                inner: ClientChannelHandle::new(inner),
                request_encoder: RequestEncoder::default(),
            };
            while let Ok((request, response_dispatcher)) = request_receiver.recv().await {
                // At the moment requests are sent sequentially, and in FIFO order. The next request
                // is sent only once a response to the previous message has been implemented.
                // TODO(#2848): Implement message prioritization, and non sequential invocations.
                let response = connector.invoke(request.as_ref());
                response_dispatcher.respond(response).unwrap();
            }
        });

        ConnectorHandle { request_dispatcher }
    }

    fn invoke(&mut self, request: &[u8]) -> Result<Vec<u8>, micro_rpc::Status> {
        let request_message = self.request_encoder.encode_request(request);
        let request_message_invocation_id = request_message.invocation_id;
        self.inner
            .write_request(request_message)
            .map_err(|_| micro_rpc::Status::new(micro_rpc::StatusCode::Internal))?;

        let (response_message, _) = self
            .inner
            .read_response()
            .map_err(|_| micro_rpc::Status::new(micro_rpc::StatusCode::Internal))?;

        // For now all messages are sent in sequence, hence we expect that the
        // id of the next response matches the preceeding request.
        // TODO(#2848): Allow messages to be sent and received out of order.
        assert_eq!(
            request_message_invocation_id,
            response_message.invocation_id
        );

        Ok(response_message.body)
    }
}

/// Implementation of an [`micro_rpc::AsyncTransport`] that enables client generated
/// by the micro_rpc to communicate with the [`Connector`] instance via an MPSC request-response
/// channel.
#[derive(Clone)]
pub struct ConnectorHandle {
    request_dispatcher:
        bmrng::unbounded::UnboundedRequestSender<Vec<u8>, Result<Vec<u8>, micro_rpc::Status>>,
}

#[async_trait::async_trait]
impl micro_rpc::AsyncTransport for ConnectorHandle {
    type Error = micro_rpc::Status;
    async fn invoke(&mut self, request_bytes: &[u8]) -> Result<Vec<u8>, Self::Error> {
        self.request_dispatcher
            .send_receive(request_bytes.to_vec())
            .await
            .map_err(|err| {
                micro_rpc::Status::new_with_message(
                    micro_rpc::StatusCode::Internal,
                    format!("failed when invoking the request_dispatcher: {}", err),
                )
            })?
    }
}
