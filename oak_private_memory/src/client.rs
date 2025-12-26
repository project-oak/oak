//
// Copyright 2025 The Project Oak Authors
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
use anyhow::{anyhow, Context, Result};
use async_trait::async_trait;
use futures::{channel::mpsc, SinkExt, StreamExt};
use oak_proto_rust::oak::session::v1::{SessionRequest, SessionResponse};
use oak_session::{
    attestation::AttestationType,
    channel::{SessionChannel, SessionInitializer},
    config::SessionConfig,
    handshake::HandshakeType,
    Session,
};
use prost::Message;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_service_client::SealedMemoryServiceClient;
use sealed_memory_rust_proto::{
    oak::private_memory::{SealedMemorySessionRequest, SealedMemorySessionResponse},
    prelude::v1::*,
};
use tonic::transport::Channel;

#[derive(Clone, Copy, Debug)]
pub enum SerializationFormat {
    BinaryProto,
    Json,
}

#[async_trait]
pub trait Transport {
    async fn send(&mut self, request: SessionRequest) -> Result<()>;
    async fn receive(&mut self) -> Result<SessionResponse>;
}

pub struct TonicInvokeTransport {
    tx: mpsc::Sender<SessionRequest>,
    rx: tonic::Streaming<SessionResponse>,
}

#[async_trait]
impl Transport for TonicInvokeTransport {
    async fn send(&mut self, request: SessionRequest) -> Result<()> {
        self.tx.send(request).await.map_err(|e| anyhow!(e))
    }

    async fn receive(&mut self) -> Result<SessionResponse> {
        self.rx
            .next()
            .await
            .ok_or(anyhow!("did not receive a response"))?
            .map_err(|e: tonic::Status| anyhow!(e))
    }
}

pub struct TonicStartSessionTransport {
    tx: mpsc::Sender<SealedMemorySessionRequest>,
    rx: tonic::Streaming<SealedMemorySessionResponse>,
}

#[async_trait]
impl Transport for TonicStartSessionTransport {
    async fn send(&mut self, request: SessionRequest) -> Result<()> {
        self.tx
            .send(SealedMemorySessionRequest { session_request: Some(request) })
            .await
            .map_err(|e| anyhow!(e))
    }

    async fn receive(&mut self) -> Result<SessionResponse> {
        let response = self
            .rx
            .next()
            .await
            .ok_or(anyhow!("did not receive a response"))?
            .map_err(|e: tonic::Status| anyhow!(e))?;
        response.session_response.ok_or(anyhow!("empty session response"))
    }
}

macro_rules! expect_response_type {
    ($response:expr, $variant:path) => {
        match $response {
            $variant(resp) => Ok(resp),
            _ => Err(anyhow!("unexpected response type")),
        }
    };
}

pub struct PrivateMemoryClient {
    client_session: oak_session::ClientSession,
    transport: Box<dyn Transport + Send>,
    format: SerializationFormat,
}

impl PrivateMemoryClient {
    pub async fn new(
        mut transport: Box<dyn Transport + Send>,
        pm_uid: &str,
        kek: &[u8],
        format: SerializationFormat,
    ) -> Result<Self> {
        let mut client_session = oak_session::ClientSession::create(
            SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build(),
        )
        .context("failed to create client session")?;

        while !client_session.is_open() {
            let request =
                client_session.next_init_message().context("failed to get next init message")?;
            transport.send(request).await.context("failed to send init message")?;
            if !client_session.is_open() {
                let response =
                    transport.receive().await.context("failed to receive init message")?;
                client_session
                    .handle_init_message(response)
                    .context("failed to handle init message")?;
            }
        }

        let mut client = Self { client_session, transport, format };

        client.register_user(pm_uid, kek).await?;
        match client.key_sync(pm_uid, kek).await {
            Ok(key_sync_response::Status::Success) => Ok(client),
            Ok(s) => Err(anyhow!("key sync failed with status: {:?}", s)),
            Err(e) => Err(e),
        }
    }

    pub async fn create_with_start_session(
        server_addr: &str,
        pm_uid: &str,
        kek: &[u8],
        format: SerializationFormat,
    ) -> Result<Self> {
        let channel = Channel::from_shared(server_addr.to_string())
            .context("failed to create shared channel")?
            .connect()
            .await
            .context("failed to connect to server")?;
        let mut client = SealedMemoryServiceClient::new(channel);
        let (tx, rx_stream) = mpsc::channel(10);
        let rx =
            client.start_session(rx_stream).await.context("failed to start session")?.into_inner();

        let transport = Box::new(TonicStartSessionTransport { tx, rx });

        Self::new(transport, pm_uid, kek, format).await
    }

    async fn invoke(
        &mut self,
        request: sealed_memory_request::Request,
    ) -> Result<sealed_memory_response::Response> {
        let sealed_memory_request =
            SealedMemoryRequest { request: Some(request), ..Default::default() };

        let payload = match self.format {
            SerializationFormat::BinaryProto => sealed_memory_request.encode_to_vec(),
            SerializationFormat::Json => {
                serde_json::to_vec(&sealed_memory_request).context("failed to serialize request")?
            }
        };

        let encrypted_request =
            self.client_session.encrypt(payload).context("failed to encrypt request")?;
        self.transport.send(encrypted_request).await.context("failed to send request")?;

        let response = self.transport.receive().await.context("failed to receive response")?;
        let decrypted_response =
            self.client_session.decrypt(response).context("failed to decrypt response")?;

        let sealed_memory_response = match self.format {
            SerializationFormat::BinaryProto => {
                SealedMemoryResponse::decode(decrypted_response.as_ref())
                    .context("failed to decode response")?
            }
            SerializationFormat::Json => serde_json::from_slice(&decrypted_response)
                .context("failed to deserialize response")?,
        };

        sealed_memory_response.response.ok_or_else(|| anyhow!("empty response"))
    }

    pub async fn register_user(
        &mut self,
        pm_uid: &str,
        kek: &[u8],
    ) -> Result<user_registration_response::Status> {
        let request = UserRegistrationRequest {
            pm_uid: pm_uid.to_string(),
            key_encryption_key: kek.to_vec(),
            boot_strap_info: Some(KeyDerivationInfo::default()),
        };
        let response =
            self.invoke(sealed_memory_request::Request::UserRegistrationRequest(request)).await?;
        match response {
            sealed_memory_response::Response::UserRegistrationResponse(resp) => Ok(resp.status()),
            _ => Err(anyhow!("unexpected response type for user registration")),
        }
    }

    pub async fn key_sync(
        &mut self,
        pm_uid: &str,
        kek: &[u8],
    ) -> Result<key_sync_response::Status> {
        let request =
            KeySyncRequest { pm_uid: pm_uid.to_string(), key_encryption_key: kek.to_vec() };
        let response = self.invoke(sealed_memory_request::Request::KeySyncRequest(request)).await?;
        match response {
            sealed_memory_response::Response::KeySyncResponse(resp) => Ok(resp.status()),
            _ => Err(anyhow!("unexpected response type for key sync")),
        }
    }

    pub async fn add_memory(&mut self, memory: Memory) -> Result<AddMemoryResponse> {
        let request = AddMemoryRequest { memory: Some(memory) };
        let response =
            self.invoke(sealed_memory_request::Request::AddMemoryRequest(request)).await?;
        expect_response_type!(response, sealed_memory_response::Response::AddMemoryResponse)
    }

    pub async fn get_memories(
        &mut self,
        tag: &str,
        page_size: i32,
        result_mask: Option<ResultMask>,
        page_token: &str,
    ) -> Result<GetMemoriesResponse> {
        let request = GetMemoriesRequest {
            tag: tag.to_string(),
            page_size,
            result_mask,
            page_token: page_token.to_string(),
        };
        let response =
            self.invoke(sealed_memory_request::Request::GetMemoriesRequest(request)).await?;
        expect_response_type!(response, sealed_memory_response::Response::GetMemoriesResponse)
    }

    pub async fn get_memory_by_id(
        &mut self,
        id: &str,
        result_mask: Option<ResultMask>,
    ) -> Result<GetMemoryByIdResponse> {
        let request = GetMemoryByIdRequest { id: id.to_string(), result_mask };
        let response =
            self.invoke(sealed_memory_request::Request::GetMemoryByIdRequest(request)).await?;
        expect_response_type!(response, sealed_memory_response::Response::GetMemoryByIdResponse)
    }

    pub async fn search_memory(
        &mut self,
        query: SearchMemoryQuery,
        page_size: i32,
        result_mask: Option<ResultMask>,
        page_token: &str,
        keep_all_llm_views: bool,
    ) -> Result<SearchMemoryResponse> {
        let request = SearchMemoryRequest {
            query: Some(query),
            page_size,
            result_mask,
            page_token: page_token.to_string(),
            keep_all_llm_views,
        };
        let response =
            self.invoke(sealed_memory_request::Request::SearchMemoryRequest(request)).await?;
        expect_response_type!(response, sealed_memory_response::Response::SearchMemoryResponse)
    }

    pub async fn delete_memory(&mut self, ids: Vec<String>) -> Result<DeleteMemoryResponse> {
        let request = DeleteMemoryRequest { ids };
        let response =
            self.invoke(sealed_memory_request::Request::DeleteMemoryRequest(request)).await?;
        expect_response_type!(response, sealed_memory_response::Response::DeleteMemoryResponse)
    }

    pub async fn reset_memory(&mut self) -> Result<ResetMemoryResponse> {
        let request = ResetMemoryRequest::default();
        let response =
            self.invoke(sealed_memory_request::Request::ResetMemoryRequest(request)).await?;
        expect_response_type!(response, sealed_memory_response::Response::ResetMemoryResponse)
    }
}
