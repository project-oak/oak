#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct InitializeRequest {
    #[prost(bytes = "vec", tag = "1")]
    pub wasm_module: ::prost::alloc::vec::Vec<u8>,
    #[prost(uint32, tag = "2")]
    pub constant_response_size: u32,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct InitializeResponse {
    #[prost(message, optional, tag = "2")]
    pub evidence: ::core::option::Option<crate::oak::attestation::v1::Evidence>,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct InvokeRequest {
    #[prost(message, optional, tag = "2")]
    pub encrypted_request: ::core::option::Option<
        crate::oak::crypto::v1::EncryptedRequest,
    >,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct InvokeResponse {
    #[prost(message, optional, tag = "2")]
    pub encrypted_response: ::core::option::Option<
        crate::oak::crypto::v1::EncryptedResponse,
    >,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct LookupDataEntry {
    #[prost(bytes = "bytes", tag = "1")]
    pub key: ::prost::bytes::Bytes,
    #[prost(bytes = "bytes", tag = "2")]
    pub value: ::prost::bytes::Bytes,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct LookupDataChunk {
    #[prost(message, repeated, tag = "1")]
    pub items: ::prost::alloc::vec::Vec<LookupDataEntry>,
}
/// If the definition of ExtendNextLookupData changes, the estimation of the size
/// when serialized in the Oak Functions Launcher needs to change, too.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct ExtendNextLookupDataRequest {
    #[prost(oneof = "extend_next_lookup_data_request::Data", tags = "1, 2")]
    pub data: ::core::option::Option<extend_next_lookup_data_request::Data>,
}
/// Nested message and enum types in `ExtendNextLookupDataRequest`.
pub mod extend_next_lookup_data_request {
    #[allow(clippy::derive_partial_eq_without_eq)]
    #[derive(Clone, PartialEq, ::prost_derive::Oneof)]
    pub enum Data {
        #[prost(message, tag = "1")]
        Chunk(super::LookupDataChunk),
        /// Experimental: a serialized array of varint-prefixed `LookupDataEntry`
        /// values. See
        /// <https://docs.rs/prost/latest/prost/fn.decode_length_delimiter.html> for
        /// more details; the hope here is that by serializing one entry at a time we
        /// can be more efficient.
        #[prost(bytes, tag = "2")]
        LengthDelimitedEntries(::prost::bytes::Bytes),
    }
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct ExtendNextLookupDataResponse {}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct FinishNextLookupDataRequest {}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct FinishNextLookupDataResponse {}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct AbortNextLookupDataResponse {}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct Empty {}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct ReserveRequest {
    #[prost(uint64, tag = "1")]
    pub additional_entries: u64,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct ReserveResponse {}
#[derive(Clone)]
pub struct OakFunctionsServer<S> {
    service: S,
}
impl<S: OakFunctions> ::micro_rpc::Transport for OakFunctionsServer<S> {
    fn invoke(
        &mut self,
        request_bytes: &[u8],
    ) -> Result<::prost::alloc::vec::Vec<u8>, !> {
        let response: ::micro_rpc::ResponseWrapper = self
            .invoke_inner(request_bytes)
            .into();
        let response_bytes = response.encode_to_vec();
        Ok(response_bytes)
    }
}
impl<S: OakFunctions> OakFunctionsServer<S> {
    pub fn new(service: S) -> Self {
        Self { service }
    }
    fn invoke_inner(
        &mut self,
        request_bytes: &[u8],
    ) -> Result<::prost::alloc::vec::Vec<u8>, ::micro_rpc::Status> {
        let request = ::micro_rpc::RequestWrapper::decode(request_bytes)
            .map_err(|err| {
                ::micro_rpc::Status::new_with_message(
                    ::micro_rpc::StatusCode::Internal,
                    ::micro_rpc::format!(
                        "Client failed to deserialize the response: {:?}", err
                    ),
                )
            })?;
        match request.method_id {
            0 => {
                let request = <InitializeRequest>::decode(request.body.as_ref())
                    .map_err(|err| {
                        ::micro_rpc::Status::new_with_message(
                            ::micro_rpc::StatusCode::Internal,
                            ::micro_rpc::format!(
                                "Service failed to deserialize the request: {:?}", err
                            ),
                        )
                    })?;
                let response = self.service.initialize(request)?;
                let response_body = response.encode_to_vec();
                Ok(response_body)
            }
            1 => {
                let request = <InvokeRequest>::decode(request.body.as_ref())
                    .map_err(|err| {
                        ::micro_rpc::Status::new_with_message(
                            ::micro_rpc::StatusCode::Internal,
                            ::micro_rpc::format!(
                                "Service failed to deserialize the request: {:?}", err
                            ),
                        )
                    })?;
                let response = self.service.handle_user_request(request)?;
                let response_body = response.encode_to_vec();
                Ok(response_body)
            }
            2 => {
                let request = <ExtendNextLookupDataRequest>::decode(
                        request.body.as_ref(),
                    )
                    .map_err(|err| {
                        ::micro_rpc::Status::new_with_message(
                            ::micro_rpc::StatusCode::Internal,
                            ::micro_rpc::format!(
                                "Service failed to deserialize the request: {:?}", err
                            ),
                        )
                    })?;
                let response = self.service.extend_next_lookup_data(request)?;
                let response_body = response.encode_to_vec();
                Ok(response_body)
            }
            3 => {
                let request = <FinishNextLookupDataRequest>::decode(
                        request.body.as_ref(),
                    )
                    .map_err(|err| {
                        ::micro_rpc::Status::new_with_message(
                            ::micro_rpc::StatusCode::Internal,
                            ::micro_rpc::format!(
                                "Service failed to deserialize the request: {:?}", err
                            ),
                        )
                    })?;
                let response = self.service.finish_next_lookup_data(request)?;
                let response_body = response.encode_to_vec();
                Ok(response_body)
            }
            4 => {
                let request = <Empty>::decode(request.body.as_ref())
                    .map_err(|err| {
                        ::micro_rpc::Status::new_with_message(
                            ::micro_rpc::StatusCode::Internal,
                            ::micro_rpc::format!(
                                "Service failed to deserialize the request: {:?}", err
                            ),
                        )
                    })?;
                let response = self.service.abort_next_lookup_data(request)?;
                let response_body = response.encode_to_vec();
                Ok(response_body)
            }
            5 => {
                let request = <LookupDataChunk>::decode(request.body.as_ref())
                    .map_err(|err| {
                        ::micro_rpc::Status::new_with_message(
                            ::micro_rpc::StatusCode::Internal,
                            ::micro_rpc::format!(
                                "Service failed to deserialize the request: {:?}", err
                            ),
                        )
                    })?;
                let response = self.service.stream_lookup_data(request)?;
                let response_body = response.encode_to_vec();
                Ok(response_body)
            }
            6 => {
                let request = <ReserveRequest>::decode(request.body.as_ref())
                    .map_err(|err| {
                        ::micro_rpc::Status::new_with_message(
                            ::micro_rpc::StatusCode::Internal,
                            ::micro_rpc::format!(
                                "Service failed to deserialize the request: {:?}", err
                            ),
                        )
                    })?;
                let response = self.service.reserve(request)?;
                let response_body = response.encode_to_vec();
                Ok(response_body)
            }
            _ => Err(::micro_rpc::Status::new(::micro_rpc::StatusCode::Unimplemented)),
        }
    }
}
pub trait OakFunctions: Sized {
    fn initialize(
        &self,
        request: InitializeRequest,
    ) -> Result<InitializeResponse, ::micro_rpc::Status>;
    fn handle_user_request(
        &self,
        request: InvokeRequest,
    ) -> Result<InvokeResponse, ::micro_rpc::Status>;
    fn extend_next_lookup_data(
        &self,
        request: ExtendNextLookupDataRequest,
    ) -> Result<ExtendNextLookupDataResponse, ::micro_rpc::Status>;
    fn finish_next_lookup_data(
        &self,
        request: FinishNextLookupDataRequest,
    ) -> Result<FinishNextLookupDataResponse, ::micro_rpc::Status>;
    fn abort_next_lookup_data(
        &self,
        request: Empty,
    ) -> Result<AbortNextLookupDataResponse, ::micro_rpc::Status>;
    fn stream_lookup_data(
        &self,
        request: LookupDataChunk,
    ) -> Result<FinishNextLookupDataResponse, ::micro_rpc::Status>;
    fn reserve(
        &self,
        request: ReserveRequest,
    ) -> Result<ReserveResponse, ::micro_rpc::Status>;
}
pub struct OakFunctionsClient<T: ::micro_rpc::Transport> {
    transport: T,
}
impl<T: ::micro_rpc::Transport> OakFunctionsClient<T> {
    pub fn new(transport: T) -> Self {
        Self { transport }
    }
    pub fn initialize(
        &mut self,
        request: &InitializeRequest,
    ) -> Result<Result<InitializeResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::client_invoke(&mut self.transport, 0, request)
    }
    pub fn handle_user_request(
        &mut self,
        request: &InvokeRequest,
    ) -> Result<Result<InvokeResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::client_invoke(&mut self.transport, 1, request)
    }
    pub fn extend_next_lookup_data(
        &mut self,
        request: &ExtendNextLookupDataRequest,
    ) -> Result<Result<ExtendNextLookupDataResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::client_invoke(&mut self.transport, 2, request)
    }
    pub fn finish_next_lookup_data(
        &mut self,
        request: &FinishNextLookupDataRequest,
    ) -> Result<Result<FinishNextLookupDataResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::client_invoke(&mut self.transport, 3, request)
    }
    pub fn abort_next_lookup_data(
        &mut self,
        request: &Empty,
    ) -> Result<Result<AbortNextLookupDataResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::client_invoke(&mut self.transport, 4, request)
    }
    pub fn stream_lookup_data(
        &mut self,
        request: &LookupDataChunk,
    ) -> Result<Result<FinishNextLookupDataResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::client_invoke(&mut self.transport, 5, request)
    }
    pub fn reserve(
        &mut self,
        request: &ReserveRequest,
    ) -> Result<Result<ReserveResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::client_invoke(&mut self.transport, 6, request)
    }
}
pub struct OakFunctionsAsyncClient<T: ::micro_rpc::AsyncTransport> {
    transport: T,
}
impl<T: ::micro_rpc::AsyncTransport> OakFunctionsAsyncClient<T> {
    pub fn new(transport: T) -> Self {
        Self { transport }
    }
    pub async fn initialize(
        &mut self,
        request: &InitializeRequest,
    ) -> Result<Result<InitializeResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::async_client_invoke(&mut self.transport, 0, request).await
    }
    pub async fn handle_user_request(
        &mut self,
        request: &InvokeRequest,
    ) -> Result<Result<InvokeResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::async_client_invoke(&mut self.transport, 1, request).await
    }
    pub async fn extend_next_lookup_data(
        &mut self,
        request: &ExtendNextLookupDataRequest,
    ) -> Result<Result<ExtendNextLookupDataResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::async_client_invoke(&mut self.transport, 2, request).await
    }
    pub async fn finish_next_lookup_data(
        &mut self,
        request: &FinishNextLookupDataRequest,
    ) -> Result<Result<FinishNextLookupDataResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::async_client_invoke(&mut self.transport, 3, request).await
    }
    pub async fn abort_next_lookup_data(
        &mut self,
        request: &Empty,
    ) -> Result<Result<AbortNextLookupDataResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::async_client_invoke(&mut self.transport, 4, request).await
    }
    pub async fn stream_lookup_data(
        &mut self,
        request: &LookupDataChunk,
    ) -> Result<Result<FinishNextLookupDataResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::async_client_invoke(&mut self.transport, 5, request).await
    }
    pub async fn reserve(
        &mut self,
        request: &ReserveRequest,
    ) -> Result<Result<ReserveResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::async_client_invoke(&mut self.transport, 6, request).await
    }
}
