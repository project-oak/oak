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

//! Cryptographic pseudo-Node functionality.

use crate::{
    io::{Receiver, ReceiverExt},
    node::invocation::InvocationExt,
    proto::oak::invocation::GrpcInvocation as Invocation,
    RuntimeProxy,
};
use log::{debug, error, info};
use oak_abi::OakStatus;
use oak_io::{handle::ReadHandle, OakError};
use oak_services::proto::{
    google::{rpc, rpc::Code},
    oak::encap::GrpcResponse,
};
use std::string::String;
use tokio::sync::oneshot;

mod tinkwrap;

/// Build an [`rpc::Status`] from a [`Code`] and a message.
pub fn rpc_status(code: Code, msg: String) -> rpc::Status {
    rpc::Status {
        code: code as i32,
        message: msg,
        details: vec![],
    }
}

/// Invoke a function of signature `(SomethingRequest) -> Result<SomethingResponse, rpc::Status>`
/// with serialized data.
fn sinvoke<T, S, F>(method: F, data: &[u8]) -> Result<Vec<u8>, rpc::Status>
where
    T: prost::Message + Default,
    S: prost::Message + Default,
    F: FnOnce(T) -> Result<S, rpc::Status>,
{
    let req = T::decode(data).map_err(|e| {
        rpc_status(
            Code::InvalidArgument,
            format!("Error decoding request: {:?}", e),
        )
    })?;
    let rsp: S = method(req)?;

    let mut rsp_data = vec![];
    rsp.encode(&mut rsp_data).map_err(|e| {
        rpc_status(
            Code::Internal,
            format!("Failed to encode response: {:?}", e),
        )
    })?;
    Ok(rsp_data)
}

/// gRPC server implementation for cryptographic pseudo-Node. Held in a separate structure from
/// [`CryptoNode`] to avoid need for `Send + Sync` support.
pub struct CryptoNodeServer {
    node_name: String,
    tink: tinkwrap::TinkWrapper,
}

impl CryptoNodeServer {
    /// Creates a new [`CryptoNode`] instance, but does not start it.
    pub fn new(node_name: &str, kms_credentials: Option<std::path::PathBuf>) -> Self {
        Self {
            node_name: node_name.to_string(),
            tink: tinkwrap::TinkWrapper::new(kms_credentials),
        }
    }

    fn invoke_method(
        &mut self,
        method_name: &str,
        req_data: &[u8],
    ) -> Result<Vec<u8>, rpc::Status> {
        // TODO(#1113): Generate this code automatically.
        match method_name {
            "/oak.crypto.OakCrypto/Generate" => sinvoke(|req| self.tink.generate(req), req_data),
            "/oak.crypto.OakCrypto/Public" => sinvoke(|req| self.tink.public(req), req_data),
            "/oak.crypto.OakCrypto/Bind" => sinvoke(|req| self.tink.bind(req), req_data),
            "/oak.crypto.OakCrypto/Unbind" => sinvoke(|req| self.tink.unbind(req), req_data),
            "/oak.crypto.OakCrypto/KMSProxy" => sinvoke(|req| self.tink.kms_proxy(req), req_data),
            "/oak.crypto.OakCrypto/Encrypt" => sinvoke(|req| self.tink.encrypt(req), req_data),
            "/oak.crypto.OakCrypto/Decrypt" => sinvoke(|req| self.tink.decrypt(req), req_data),
            "/oak.crypto.OakCrypto/EncryptDeterministically" => {
                sinvoke(|req| self.tink.encrypt_deterministically(req), req_data)
            }
            "/oak.crypto.OakCrypto/DecryptDeterministically" => {
                sinvoke(|req| self.tink.decrypt_deterministically(req), req_data)
            }
            "/oak.crypto.OakCrypto/ComputeMac" => {
                sinvoke(|req| self.tink.compute_mac(req), req_data)
            }
            "/oak.crypto.OakCrypto/VerifyMac" => sinvoke(|req| self.tink.verify_mac(req), req_data),
            "/oak.crypto.OakCrypto/ComputePrf" => {
                sinvoke(|req| self.tink.compute_prf(req), req_data)
            }
            "/oak.crypto.OakCrypto/Sign" => sinvoke(|req| self.tink.sign(req), req_data),
            "/oak.crypto.OakCrypto/Verify" => sinvoke(|req| self.tink.verify(req), req_data),
            _ => Err(rpc_status(
                Code::NotFound,
                format!("Unknown method_name: {}", method_name),
            )),
        }
    }

    /// Process a gRPC invocation.
    fn process_invocation(&mut self, runtime: &RuntimeProxy, invocation: &Invocation) {
        let grpc_response = match invocation.receive_request(runtime) {
            Ok(request) => {
                debug!("{}: invoke method {}", self.node_name, request.method_name);
                let result = self.invoke_method(&request.method_name, &request.req_msg);
                match result {
                    Ok(data) => GrpcResponse {
                        rsp_msg: data,
                        status: None,
                        last: true,
                    },
                    Err(grpc_err) => GrpcResponse {
                        rsp_msg: vec![],
                        status: Some(grpc_err),
                        last: true,
                    },
                }
            }
            Err(error) => GrpcResponse {
                rsp_msg: vec![],
                status: Some(rpc_status(
                    Code::InvalidArgument,
                    format!("Error reading request: {:?}", error),
                )),
                last: true,
            },
        };
        if let Err(e) = invocation.send_response(grpc_response, runtime) {
            error!("Couldn't send the gRPC response: {:?}", e);
        }
    }
}

/// Cryptographic pseudo-Node.
pub struct CryptoNode {
    node_name: String,
    kms_credentials: Option<std::path::PathBuf>,
}

impl CryptoNode {
    /// Creates a new [`CryptoNode`] instance, but does not start it.
    pub fn new(node_name: &str, kms_credentials: Option<std::path::PathBuf>) -> Self {
        Self {
            node_name: node_name.to_string(),
            kms_credentials,
        }
    }
}

impl super::Node for CryptoNode {
    fn node_type(&self) -> &'static str {
        "crypto"
    }

    /// Main execution loop for the crypto pseudo-Node.
    fn run(
        self: Box<Self>,
        runtime: RuntimeProxy,
        handle: oak_abi::Handle,
        _notify_receiver: oneshot::Receiver<()>,
    ) {
        info!("{}: Starting crypto pseudo-Node", self.node_name);

        let mut server = CryptoNodeServer::new(&self.node_name, self.kms_credentials.clone());

        // Create a [`Receiver`] used for reading gRPC invocations.
        let receiver = Receiver::<Invocation>::new(ReadHandle { handle });
        loop {
            debug!("Waiting for gRPC invocation");
            match receiver.receive(&runtime) {
                Ok(invocation) => {
                    server.process_invocation(&runtime, &invocation);
                    invocation.close(&runtime);
                }
                Err(OakError::OakStatus(OakStatus::ErrTerminated)) => {
                    break;
                }
                Err(error) => {
                    error!("Couldn't receive the invocation: {:?}", error);
                    break;
                }
            }
        }
        let _ = runtime.channel_close(handle);
        info!("{} crypto pseudo-Node execution complete", self.node_name);
    }
}
