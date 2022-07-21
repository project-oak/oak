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

//! This crate contains tests for the `oak_idl_gen_structs` and `oak_idl_gen_services` crates. It
//! needs to be separate from them in order to be able to invoke them at build time.

extern crate alloc;

use oak_idl::Handler;

mod test_schema {
    #![allow(clippy::derivable_impls, clippy::needless_borrow)]
    #![allow(dead_code, unused_imports)]

    include!(concat!(env!("OUT_DIR"), "/test_schema_generated.rs"));
    include!(concat!(env!("OUT_DIR"), "/test_schema_services_servers.rs"));
    include!(concat!(env!("OUT_DIR"), "/test_schema_services_clients.rs"));
    include!(concat!(
        env!("OUT_DIR"),
        "/test_schema_services_async_clients.rs"
    ));
}

struct TestServiceImpl;

/// An implementation of the [`test_schema::TestService`] service trait for testing.
impl test_schema::TestService for TestServiceImpl {
    fn lookup_data(
        &mut self,
        request: &test_schema::LookupDataRequest,
    ) -> Result<oak_idl::utils::OwnedFlatbuffer<test_schema::LookupDataResponse>, oak_idl::Status>
    {
        let h = maplit::hashmap! {
            vec![14, 12] => vec![19, 88]
        };
        let mut b = oak_idl::utils::OwnedFlatbufferBuilder::default();
        let value = h
            .get(request.key().unwrap())
            .map(|v| b.create_vector::<u8>(v));
        let flatbuffer = test_schema::LookupDataResponse::create(
            &mut b,
            &test_schema::LookupDataResponseArgs { value },
        );
        let owned_flatbuffer = b.finish(flatbuffer).map_err(|err| {
            oak_idl::Status::new_with_message(
                oak_idl::StatusCode::Internal,
                format!("failed to build response: {:?}", err),
            )
        })?;
        Ok(owned_flatbuffer)
    }

    fn log(
        &mut self,
        request: &test_schema::LogRequest,
    ) -> Result<oak_idl::utils::OwnedFlatbuffer<test_schema::LogResponse>, oak_idl::Status> {
        eprintln!("log: {}", request.entry().unwrap());
        let mut b = oak_idl::utils::OwnedFlatbufferBuilder::default();
        let flatbuffer = test_schema::LogResponse::create(&mut b, &test_schema::LogResponseArgs {});
        let owned_flatbuffer = b.finish(flatbuffer).map_err(|err| {
            oak_idl::Status::new_with_message(
                oak_idl::StatusCode::Internal,
                format!("failed to build response: {:?}", err),
            )
        })?;
        Ok(owned_flatbuffer)
    }
}

#[test]
fn test_lookup_data() {
    let service = TestServiceImpl;
    use test_schema::TestService;
    let handler = service.serve();
    let mut client = test_schema::TestServiceClient::new(handler);
    {
        let mut builder = oak_idl::utils::OwnedFlatbufferBuilder::default();
        let key = builder.create_vector::<u8>(&[14, 12]);
        let flatbuffer = test_schema::LookupDataRequest::create(
            &mut builder,
            &test_schema::LookupDataRequestArgs { key: Some(key) },
        );
        let owned_flatbuffer = builder.finish(flatbuffer).unwrap();
        let response = client.lookup_data(owned_flatbuffer.into_vec()).unwrap();
        assert_eq!(Some([19, 88].as_ref()), response.get().value());
    }
    {
        let mut builder = oak_idl::utils::OwnedFlatbufferBuilder::default();
        let key = builder.create_vector::<u8>(&[10, 00]);
        let flatbuffer = test_schema::LookupDataRequest::create(
            &mut builder,
            &test_schema::LookupDataRequestArgs { key: Some(key) },
        );
        let owned_flatbuffer = builder.finish(flatbuffer).unwrap();
        let response = client.lookup_data(owned_flatbuffer.into_vec()).unwrap();
        assert_eq!(None, response.get().value());
    }
}

/// Simple async wrapper around the synchronous server.
/// Used to test async clients that expect an async handler.
pub struct AsyncTestServiceServer<S: test_schema::TestService> {
    inner: test_schema::TestServiceServer<S>,
}

#[async_trait::async_trait]
impl<S: test_schema::TestService + std::marker::Send + std::marker::Sync> oak_idl::AsyncHandler
    for AsyncTestServiceServer<S>
{
    async fn invoke(
        &mut self,
        request: oak_idl::Request,
    ) -> Result<alloc::vec::Vec<u8>, oak_idl::Status> {
        self.inner.invoke(request)
    }
}

#[tokio::test]
async fn test_async_lookup_data() {
    let service = TestServiceImpl;
    use test_schema::TestService;
    let service_impl = service.serve();
    let async_handler = AsyncTestServiceServer {
        inner: service_impl,
    };
    let mut client = test_schema::TestServiceAsyncClient::new(async_handler);
    {
        let mut builder = oak_idl::utils::OwnedFlatbufferBuilder::default();
        let key = builder.create_vector::<u8>(&[14, 12]);
        let flatbuffer = test_schema::LookupDataRequest::create(
            &mut builder,
            &test_schema::LookupDataRequestArgs { key: Some(key) },
        );
        let owned_flatbuffer = builder.finish(flatbuffer).unwrap();
        let response = client
            .lookup_data(owned_flatbuffer.into_vec())
            .await
            .unwrap();
        assert_eq!(Some([19, 88].as_ref()), response.get().value());
    }
    {
        let mut builder = oak_idl::utils::OwnedFlatbufferBuilder::default();
        let key = builder.create_vector::<u8>(&[10, 00]);
        let flatbuffer = test_schema::LookupDataRequest::create(
            &mut builder,
            &test_schema::LookupDataRequestArgs { key: Some(key) },
        );
        let owned_flatbuffer = builder.finish(flatbuffer).unwrap();
        let response = client
            .lookup_data(owned_flatbuffer.into_vec())
            .await
            .unwrap();
        assert_eq!(None, response.get().value());
    }
}
