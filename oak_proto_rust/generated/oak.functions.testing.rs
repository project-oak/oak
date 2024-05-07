#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct LookupRequest {
    #[prost(bytes = "vec", repeated, tag = "1")]
    pub keys: ::prost::alloc::vec::Vec<::prost::alloc::vec::Vec<u8>>,
    #[prost(enumeration = "lookup_request::Mode", tag = "2")]
    pub mode: i32,
}
/// Nested message and enum types in `LookupRequest`.
pub mod lookup_request {
    #[derive(
        Clone,
        Copy,
        Debug,
        PartialEq,
        Eq,
        Hash,
        PartialOrd,
        Ord,
        ::prost::Enumeration
    )]
    #[repr(i32)]
    pub enum Mode {
        Individual = 0,
        Batch = 1,
    }
    impl Mode {
        /// String value of the enum field names used in the ProtoBuf definition.
        ///
        /// The values are not transformed in any way and thus are considered stable
        /// (if the ProtoBuf definition does not change) and safe for programmatic use.
        pub fn as_str_name(&self) -> &'static str {
            match self {
                Mode::Individual => "INDIVIDUAL",
                Mode::Batch => "BATCH",
            }
        }
        /// Creates an enum from field names used in the ProtoBuf definition.
        pub fn from_str_name(value: &str) -> ::core::option::Option<Self> {
            match value {
                "INDIVIDUAL" => Some(Self::Individual),
                "BATCH" => Some(Self::Batch),
                _ => None,
            }
        }
    }
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct LookupResponse {
    #[prost(bytes = "vec", repeated, tag = "1")]
    pub values: ::prost::alloc::vec::Vec<::prost::alloc::vec::Vec<u8>>,
}
/// Echo the bytes back, and then panic.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct EchoAndPanicRequest {
    #[prost(bytes = "vec", tag = "5")]
    pub data: ::prost::alloc::vec::Vec<u8>,
}
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct EchoAndPanicResponse {
    #[prost(bytes = "vec", tag = "2")]
    pub data: ::prost::alloc::vec::Vec<u8>,
}
#[derive(Clone)]
pub struct TestModuleServer<S> {
    service: S,
}
impl<S: TestModule> ::micro_rpc::Transport for TestModuleServer<S> {
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
impl<S: TestModule> TestModuleServer<S> {
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
                let request = <LookupRequest>::decode(request.body.as_ref())
                    .map_err(|err| {
                        ::micro_rpc::Status::new_with_message(
                            ::micro_rpc::StatusCode::Internal,
                            ::micro_rpc::format!(
                                "Service failed to deserialize the request: {:?}", err
                            ),
                        )
                    })?;
                let response = self.service.lookup(request)?;
                let response_body = response.encode_to_vec();
                Ok(response_body)
            }
            1 => {
                let request = <EchoAndPanicRequest>::decode(request.body.as_ref())
                    .map_err(|err| {
                        ::micro_rpc::Status::new_with_message(
                            ::micro_rpc::StatusCode::Internal,
                            ::micro_rpc::format!(
                                "Service failed to deserialize the request: {:?}", err
                            ),
                        )
                    })?;
                let response = self.service.echo_and_panic(request)?;
                let response_body = response.encode_to_vec();
                Ok(response_body)
            }
            _ => Err(::micro_rpc::Status::new(::micro_rpc::StatusCode::Unimplemented)),
        }
    }
}
pub trait TestModule: Sized {
    fn lookup(
        &mut self,
        request: LookupRequest,
    ) -> Result<LookupResponse, ::micro_rpc::Status>;
    fn echo_and_panic(
        &mut self,
        request: EchoAndPanicRequest,
    ) -> Result<EchoAndPanicResponse, ::micro_rpc::Status>;
}
pub struct TestModuleClient<T: ::micro_rpc::Transport> {
    transport: T,
}
impl<T: ::micro_rpc::Transport> TestModuleClient<T> {
    pub fn new(transport: T) -> Self {
        Self { transport }
    }
    pub fn lookup(
        &mut self,
        request: &LookupRequest,
    ) -> Result<Result<LookupResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::client_invoke(&mut self.transport, 0, request)
    }
    pub fn echo_and_panic(
        &mut self,
        request: &EchoAndPanicRequest,
    ) -> Result<Result<EchoAndPanicResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::client_invoke(&mut self.transport, 1, request)
    }
}
pub struct TestModuleAsyncClient<T: ::micro_rpc::AsyncTransport> {
    transport: T,
}
impl<T: ::micro_rpc::AsyncTransport> TestModuleAsyncClient<T> {
    pub fn new(transport: T) -> Self {
        Self { transport }
    }
    pub async fn lookup(
        &mut self,
        request: &LookupRequest,
    ) -> Result<Result<LookupResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::async_client_invoke(&mut self.transport, 0, request).await
    }
    pub async fn echo_and_panic(
        &mut self,
        request: &EchoAndPanicRequest,
    ) -> Result<Result<EchoAndPanicResponse, ::micro_rpc::Status>, T::Error> {
        ::micro_rpc::async_client_invoke(&mut self.transport, 1, request).await
    }
}
