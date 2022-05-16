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

mod oak {
    #![allow(clippy::derivable_impls, clippy::needless_borrow)]
    #![allow(dead_code, unused_imports)]

    include!(concat!(env!("OUT_DIR"), "/oak_generated.rs"));
    include!(concat!(env!("OUT_DIR"), "/oak_services.rs"));
}

struct OakImpl;

/// An implementation of the [`Oak`] service trait for testing.
impl oak::Oak for OakImpl {
    fn lookup_data(
        &self,
        request: &oak::LookupDataRequest,
    ) -> oak_idl::Message<oak::LookupDataResponse> {
        let h = maplit::hashmap! {
            vec![14, 12] => vec![19, 88]
        };
        let mut b = oak_idl::MessageBuilder::default();
        let value = h
            .get(request.key().unwrap())
            .map(|v| b.create_vector::<u8>(v));
        let m = oak::LookupDataResponse::create(&mut b, &oak::LookupDataResponseArgs { value });
        b.finish(m).unwrap()
    }

    fn log(&self, request: &oak::LogRequest) -> oak_idl::Message<oak::LogResponse> {
        eprintln!("log: {}", request.entry().unwrap());
        let mut b = oak_idl::MessageBuilder::default();
        let m = oak::LogResponse::create(&mut b, &oak::LogResponseArgs {});
        b.finish(m).unwrap()
    }
}

#[test]
fn test_lookup_data() {
    let s = OakImpl;
    use oak::Oak;
    let transport = s.serve();
    let mut c = oak::OakClient::new(transport);
    {
        let mut b = oak_idl::MessageBuilder::default();
        let v = b.create_vector::<u8>(&[14, 12]);
        let req =
            oak::LookupDataRequest::create(&mut b, &oak::LookupDataRequestArgs { key: Some(v) });
        let message = b.finish(req).unwrap();
        let res = c.lookup_data(message.buf()).unwrap();
        assert_eq!(Some([19, 88].as_ref()), res.get().value());
    }
    {
        let mut b = oak_idl::MessageBuilder::default();
        let v = b.create_vector::<u8>(&[10, 00]);
        let req =
            oak::LookupDataRequest::create(&mut b, &oak::LookupDataRequestArgs { key: Some(v) });
        let message = b.finish(req).unwrap();
        let res = c.lookup_data(message.buf()).unwrap();
        assert_eq!(None, res.get().value());
    }
}
