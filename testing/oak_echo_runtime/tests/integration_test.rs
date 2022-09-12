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

#![feature(assert_matches)]

extern crate alloc;

use core::assert_matches::assert_matches;
use oak_echo_runtime::{schema::EchoRuntime, RuntimeImplementation};

mod schema {
    #![allow(clippy::derivable_impls, clippy::needless_borrow)]
    #![allow(dead_code, unused_imports)]

    include!(concat!(env!("OUT_DIR"), "/schema_generated.rs"));
    include!(concat!(env!("OUT_DIR"), "/schema_services_clients.rs"));
}

const TEST_DATA: &[u8] = b"test_data";

#[test]
fn it_should_handle_echo_requests() {
    let runtime = RuntimeImplementation::new();
    let mut client = schema::EchoRuntimeClient::new(EchoRuntime::serve(runtime));

    let owned_request_flatbuffer = {
        let mut builder = oak_idl::utils::OwnedFlatbufferBuilder::default();
        let body = builder.create_vector::<u8>(&TEST_DATA);
        let flatbuffer = schema::EchoRequest::create(
            &mut builder,
            &schema::EchoRequestArgs { body: Some(body) },
        );
        builder
            .finish(flatbuffer)
            .map_err(|err| {
                oak_idl::Status::new_with_message(oak_idl::StatusCode::Internal, err.to_string())
            })
            .unwrap()
    };
    let result = client.echo(owned_request_flatbuffer.into_vec());

    assert_matches!(result, Ok(_));
    assert_matches!(result.unwrap().get().body(), Some(body) if body == TEST_DATA);
}
