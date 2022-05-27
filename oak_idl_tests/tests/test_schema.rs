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

mod test_schema {
    #![allow(clippy::derivable_impls, clippy::needless_borrow)]
    #![allow(dead_code, unused_imports)]

    include!(concat!(env!("OUT_DIR"), "/test_schema_generated.rs"));
    include!(concat!(env!("OUT_DIR"), "/test_schema_services.rs"));
}

struct TestServiceImpl;

/// An implementation of the [`test_schema::TestService`] service trait for testing.
impl test_schema::TestService for TestServiceImpl {
    fn lookup_data(
        &self,
        request: &test_schema::LookupDataRequest,
    ) -> oak_idl::utils::Message<test_schema::LookupDataResponse> {
        let h = maplit::hashmap! {
            vec![14, 12] => vec![19, 88]
        };
        let mut b = oak_idl::utils::MessageBuilder::default();
        let value = h
            .get(request.key().unwrap())
            .map(|v| b.create_vector::<u8>(v));
        let m = test_schema::LookupDataResponse::create(
            &mut b,
            &test_schema::LookupDataResponseArgs { value },
        );
        b.finish(m).unwrap()
    }

    fn log(
        &self,
        request: &test_schema::LogRequest,
    ) -> oak_idl::utils::Message<test_schema::LogResponse> {
        eprintln!("log: {}", request.entry().unwrap());
        let mut b = oak_idl::utils::MessageBuilder::default();
        let m = test_schema::LogResponse::create(&mut b, &test_schema::LogResponseArgs {});
        b.finish(m).unwrap()
    }
}

#[test]
fn test_lookup_data() {
    let service = TestServiceImpl;
    use test_schema::TestService;
    let handler = service.serve();
    let mut client = test_schema::TestServiceClient::new(handler);
    {
        let mut builder = oak_idl::utils::MessageBuilder::default();
        let key = builder.create_vector::<u8>(&[14, 12]);
        let request = test_schema::LookupDataRequest::create(
            &mut builder,
            &test_schema::LookupDataRequestArgs { key: Some(key) },
        );
        let message = builder.finish(request).unwrap();
        let response = client.lookup_data(message.buf()).unwrap();
        assert_eq!(Some([19, 88].as_ref()), response.get().value());
    }
    {
        let mut builder = oak_idl::utils::MessageBuilder::default();
        let key = builder.create_vector::<u8>(&[10, 00]);
        let request = test_schema::LookupDataRequest::create(
            &mut builder,
            &test_schema::LookupDataRequestArgs { key: Some(key) },
        );
        let message = builder.finish(request).unwrap();
        let response = client.lookup_data(message.buf()).unwrap();
        assert_eq!(None, response.get().value());
    }
}
