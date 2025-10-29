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

//! This crate contains tests for the `micro_rpc_gen_structs` and
//! `micro_rpc_gen_services` crates. It needs to be separate from them in order
//! to be able to invoke them at build time.

#![feature(never_type)]
#![feature(unwrap_infallible)]

extern crate alloc;

use micro_rpc::Transport;
use test_schema_service::micro_rpc::tests::{
    LogRequest, LogResponse, LookupDataRequest, LookupDataResponse, TestService,
    TestServiceAsyncClient, TestServiceClient, TestServiceServer,
};

/// Test implementation of a fallible transport that always returns the same
/// error.
struct FailingTransport;

impl Transport for FailingTransport {
    type Error = u32;

    fn invoke(&mut self, _request_bytes: &[u8]) -> Result<Vec<u8>, Self::Error> {
        Err(42)
    }
}

struct TestServiceImpl;

/// An implementation of the [`TestService`] service trait for
/// testing.
impl TestService for TestServiceImpl {
    fn lookup_data(
        &mut self,
        request: LookupDataRequest,
    ) -> Result<LookupDataResponse, micro_rpc::Status> {
        let h = maplit::hashmap! {
            vec![14, 12] => vec![19, 88]
        };
        h.get(&request.key).map(|v| LookupDataResponse { value: v.clone() }).ok_or_else(|| {
            micro_rpc::Status::new_with_message(micro_rpc::StatusCode::NotFound, "not found")
        })
    }

    fn log(&mut self, request: LogRequest) -> Result<LogResponse, micro_rpc::Status> {
        eprintln!("log: {}", request.entry);
        Ok(LogResponse {})
    }

    fn empty(&mut self, _request: ()) -> Result<(), ::micro_rpc::Status> {
        Ok(())
    }
    fn duration(
        &mut self,
        _request: ::prost_types::Duration,
    ) -> Result<::prost_types::Duration, ::micro_rpc::Status> {
        Ok(std::time::Duration::from_millis(123).try_into().unwrap())
    }
    fn timestamp(
        &mut self,
        _request: ::prost_types::Timestamp,
    ) -> Result<::prost_types::Timestamp, ::micro_rpc::Status> {
        Ok(std::time::SystemTime::UNIX_EPOCH.into())
    }
    fn any(
        &mut self,
        _request: ::prost_types::Any,
    ) -> Result<::prost_types::Any, ::micro_rpc::Status> {
        Ok(prost_types::Any::default())
    }
}

#[test]
fn test_failing_transport() {
    let mut client = TestServiceClient::new(FailingTransport);
    let request = LookupDataRequest { key: vec![14, 12] };
    let transport_response = client.lookup_data(&request);
    assert_eq!(Err(42), transport_response);
}

#[test]
fn test_lookup_data() {
    let service = TestServiceImpl;
    let transport = TestServiceServer::new(service);
    let mut client = TestServiceClient::new(transport);
    {
        let request = LookupDataRequest { key: vec![14, 12] };
        let response = client.lookup_data(&request).into_ok();
        assert_eq!(Ok(LookupDataResponse { value: vec![19, 88] }), response);
    }
    {
        let request = LookupDataRequest { key: vec![10, 00] };
        let response = client.lookup_data(&request).into_ok();
        assert_eq!(
            Err(micro_rpc::Status::new_with_message(micro_rpc::StatusCode::NotFound, "not found")),
            response
        );
    }
}

/// Simple async wrapper around the synchronous server.
/// Used to test async clients that expect an async transport.
pub struct AsyncTestServiceServer<S: TestService> {
    inner: TestServiceServer<S>,
}

#[async_trait::async_trait]
impl<S: TestService + std::marker::Send + std::marker::Sync> micro_rpc::AsyncTransport
    for AsyncTestServiceServer<S>
{
    async fn invoke(&mut self, request_bytes: &[u8]) -> Result<alloc::vec::Vec<u8>, !> {
        self.inner.invoke(request_bytes)
    }
}

#[tokio::test]
async fn test_async_lookup_data() {
    let service = TestServiceImpl;
    let service_impl = TestServiceServer::new(service);
    let async_transport = AsyncTestServiceServer { inner: service_impl };
    let mut client = TestServiceAsyncClient::new(async_transport);
    {
        let request = LookupDataRequest { key: vec![14, 12] };
        let response = client.lookup_data(&request).await.into_ok();
        assert_eq!(Ok(LookupDataResponse { value: vec![19, 88] }), response);
    }
    {
        let request = LookupDataRequest { key: vec![10, 00] };
        let response = client.lookup_data(&request).await.into_ok();
        assert_eq!(
            Err(micro_rpc::Status::new_with_message(micro_rpc::StatusCode::NotFound, "not found")),
            response
        );
    }
}
