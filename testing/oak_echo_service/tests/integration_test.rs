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
#![feature(never_type)]
#![feature(unwrap_infallible)]

extern crate alloc;

use oak_echo_service::EchoService;
use service::oak::echo::{EchoClient, EchoRequest, EchoServer};

const TEST_DATA: &[u8] = b"test_data";

#[test]
fn it_should_handle_echo_requests() {
    let mock_attester = oak_restricted_kernel_sdk::testing::MockAttester::create()
        .expect("couldn't create mock attester");
    let service = EchoService { attester: mock_attester };
    let mut client = EchoClient::new(EchoServer::new(service));

    let request = EchoRequest { body: TEST_DATA.to_vec() };
    let response = client.echo(&request).into_ok();

    assert!(response.is_ok());
    assert_eq!(response.unwrap().body, TEST_DATA);
}

#[test]
fn it_should_provide_evidence() {
    let mock_attester = oak_restricted_kernel_sdk::testing::MockAttester::create()
        .expect("couldn't create mock attester");
    let service = EchoService { attester: mock_attester };
    let mut client = EchoClient::new(EchoServer::new(service));

    let response = client.get_evidence(&()).into_ok();

    assert!(response.is_ok());
    assert!(response.unwrap().evidence.is_some());
}
