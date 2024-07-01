#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct ReadRequestRequest {}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct ReadRequestResponse {
    #[prost(bytes = "vec", tag = "1")]
    pub body: ::prost::alloc::vec::Vec<u8>,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct WriteResponseRequest {
    #[prost(bytes = "vec", tag = "1")]
    pub body: ::prost::alloc::vec::Vec<u8>,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct WriteResponseResponse {}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct LogRequest {
    #[prost(string, tag = "1")]
    pub message: ::prost::alloc::string::String,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct LogResponse {}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct LookupDataRequest {
    #[prost(bytes = "vec", tag = "1")]
    pub key: ::prost::alloc::vec::Vec<u8>,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct LookupDataResponse {
    #[prost(message, optional, tag = "1")]
    pub value: ::core::option::Option<::prost::alloc::vec::Vec<u8>>,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct LookupDataMultiRequest {
    #[prost(bytes = "vec", repeated, tag = "1")]
    pub keys: ::prost::alloc::vec::Vec<::prost::alloc::vec::Vec<u8>>,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct LookupDataMultiResponse {
    #[prost(message, repeated, tag = "1")]
    pub values: ::prost::alloc::vec::Vec<BytesValue>,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct TestRequest {
    #[prost(bytes = "vec", tag = "1")]
    pub body: ::prost::alloc::vec::Vec<u8>,
    /// Whether to echo the message back. If false, the response will be empty.
    #[prost(bool, tag = "2")]
    pub echo: bool,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct TestResponse {
    #[prost(bytes = "vec", tag = "1")]
    pub body: ::prost::alloc::vec::Vec<u8>,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost_derive::Message)]
pub struct BytesValue {
    #[prost(bytes = "vec", tag = "1")]
    pub value: ::prost::alloc::vec::Vec<u8>,
    /// If true, the value was found in the store. This is useful to distinguish
    /// between a value that was not found and a value that was found and is empty.
    #[prost(bool, tag = "2")]
    pub found: bool,
}
#[derive(Clone)]
pub struct StdWasmApiServer<S> {
    service: S,
}
impl<S: StdWasmApi> ::micro_rpc::Transport for StdWasmApiServer<S> {
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
impl<S: StdWasmApi> StdWasmApiServer<S> {
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
                let request = <ReadRequestRequest>::decode(request.body.as_ref())
                    .map_err(|err| {
                        ::micro_rpc::Status::new_with_message(
                            ::micro_rpc::StatusCode::Internal,
                            ::micro_rpc::format!(
                                "Service failed to deserialize the request: {:?}", err
                            ),
                        )
                    })?;
                let response = self.service.read_request(request)?;
                let response_body = response.encode_to_vec();
                Ok(response_body)
            }
            1 => {
                let request = <WriteResponseRequest>::decode(request.body.as_ref())
                    .map_err(|err| {
                        ::micro_rpc::Status::new_with_message(
                            ::micro_rpc::StatusCode::Internal,
                            ::micro_rpc::format!(
                                "Service failed to deserialize the request: {:?}", err
                            ),
                        )
                    })?;
                let response = self.service.write_response(request)?;
                let response_body = response.encode_to_vec();
                Ok(response_body)
            }
            2 => {
                let request = <LogRequest>::decode(request.body.as_ref())
                    .map_err(|err| {
                        ::micro_rpc::Status::new_with_message(
                            ::micro_rpc::StatusCode::Internal,
                            ::micro_rpc::format!(
                                "Service failed to deserialize the request: {:?}", err
                            ),
                        )
                    })?;
                let response = self.service.log(request)?;
                let response_body = response.encode_to_vec();
                Ok(response_body)
            }
            3 => {
                let request = <LookupDataRequest>::decode(request.body.as_ref())
                    .map_err(|err| {
                        ::micro_rpc::Status::new_with_message(
                            ::micro_rpc::StatusCode::Internal,
                            ::micro_rpc::format!(
                                "Service failed to deserialize the request: {:?}", err
                            ),
                        )
                    })?;
                let response = self.service.lookup_data(request)?;
                let response_body = response.encode_to_vec();
                Ok(response_body)
            }
            4 => {
                let request = <LookupDataMultiRequest>::decode(request.body.as_ref())
                    .map_err(|err| {
                        ::micro_rpc::Status::new_with_message(
                            ::micro_rpc::StatusCode::Internal,
                            ::micro_rpc::format!(
                                "Service failed to deserialize the request: {:?}", err
                            ),
                        )
                    })?;
                let response = self.service.lookup_data_multi(request)?;
                let response_body = response.encode_to_vec();
                Ok(response_body)
            }
            128 => {
                let request = <TestRequest>::decode(request.body.as_ref())
                    .map_err(|err| {
                        ::micro_rpc::Status::new_with_message(
                            ::micro_rpc::StatusCode::Internal,
                            ::micro_rpc::format!(
                                "Service failed to deserialize the request: {:?}", err
                            ),
                        )
                    })?;
                let response = self.service.test(request)?;
                let response_body = response.encode_to_vec();
                Ok(response_body)
            }
            _ => Err(::micro_rpc::Status::new(::micro_rpc::StatusCode::Unimplemented)),
        }
    }
}
pub trait StdWasmApi: Sized {
    fn read_request(
        &mut self,
        request: ReadRequestRequest,
    ) -> Result<ReadRequestResponse, ::micro_rpc::Status>;
    fn write_response(
        &mut self,
        request: WriteResponseRequest,
    ) -> Result<WriteResponseResponse, ::micro_rpc::Status>;
    fn log(&mut self, request: LogRequest) -> Result<LogResponse, ::micro_rpc::Status>;
    fn lookup_data(
        &mut self,
        request: LookupDataRequest,
    ) -> Result<LookupDataResponse, ::micro_rpc::Status>;
    fn lookup_data_multi(
        &mut self,
        request: LookupDataMultiRequest,
    ) -> Result<LookupDataMultiResponse, ::micro_rpc::Status>;
    fn test(
        &mut self,
        request: TestRequest,
    ) -> Result<TestResponse, ::micro_rpc::Status>;
}
pub struct StdWasmApiClient<T: ::micro_rpc::Transport> {
    transport: T,
}
impl<T: ::micro_rpc::Transport> StdWasmApiClient<T> {
    pub fn new(transport: T) -> Self {
        Self { transport }
    }
    pub fn read_request(
        &mut self,
        request: &ReadRequestRequest,
    ) -> Result<Result<ReadRequestResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::client_invoke(&mut self.transport, 0, request)
    }
    pub fn write_response(
        &mut self,
        request: &WriteResponseRequest,
    ) -> Result<Result<WriteResponseResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::client_invoke(&mut self.transport, 1, request)
    }
    pub fn log(
        &mut self,
        request: &LogRequest,
    ) -> Result<Result<LogResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::client_invoke(&mut self.transport, 2, request)
    }
    pub fn lookup_data(
        &mut self,
        request: &LookupDataRequest,
    ) -> Result<Result<LookupDataResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::client_invoke(&mut self.transport, 3, request)
    }
    pub fn lookup_data_multi(
        &mut self,
        request: &LookupDataMultiRequest,
    ) -> Result<Result<LookupDataMultiResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::client_invoke(&mut self.transport, 4, request)
    }
    pub fn test(
        &mut self,
        request: &TestRequest,
    ) -> Result<Result<TestResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::client_invoke(&mut self.transport, 128, request)
    }
}
pub struct StdWasmApiAsyncClient<T: ::micro_rpc::AsyncTransport> {
    transport: T,
}
impl<T: ::micro_rpc::AsyncTransport> StdWasmApiAsyncClient<T> {
    pub fn new(transport: T) -> Self {
        Self { transport }
    }
    pub async fn read_request(
        &mut self,
        request: &ReadRequestRequest,
    ) -> Result<Result<ReadRequestResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::async_client_invoke(&mut self.transport, 0, request).await
    }
    pub async fn write_response(
        &mut self,
        request: &WriteResponseRequest,
    ) -> Result<Result<WriteResponseResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::async_client_invoke(&mut self.transport, 1, request).await
    }
    pub async fn log(
        &mut self,
        request: &LogRequest,
    ) -> Result<Result<LogResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::async_client_invoke(&mut self.transport, 2, request).await
    }
    pub async fn lookup_data(
        &mut self,
        request: &LookupDataRequest,
    ) -> Result<Result<LookupDataResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::async_client_invoke(&mut self.transport, 3, request).await
    }
    pub async fn lookup_data_multi(
        &mut self,
        request: &LookupDataMultiRequest,
    ) -> Result<Result<LookupDataMultiResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::async_client_invoke(&mut self.transport, 4, request).await
    }
    pub async fn test(
        &mut self,
        request: &TestRequest,
    ) -> Result<Result<TestResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::async_client_invoke(&mut self.transport, 128, request).await
    }
}
