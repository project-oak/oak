//
// Copyright 2019 The Project Oak Authors
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

pub mod proto {
    include!(concat!(env!("OUT_DIR"), "/oak.examples.abitest.rs"));
}

use abitest_common::InternalMessage;
use byteorder::WriteBytesExt;
use expect::{expect, expect_eq, expect_matches};
use http::Uri;
use log::{debug, error, info, trace, warn};
use oak::{
    grpc,
    handle::is_valid,
    io::{Receiver, ReceiverExt, SenderExt},
    ChannelReadStatus, OakError, OakStatus,
};
use oak_abi::{
    label::{confidentiality_label, top, Label},
    proto::oak::application::{
        node_configuration::ConfigType, ConfigMap, CryptoConfiguration, NodeConfiguration,
        RoughtimeClientConfiguration, StorageProxyConfiguration,
    },
};
use prost::Message;
use proto::{
    AbiTestRequest, AbiTestResponse, GrpcTestRequest, GrpcTestResponse, OakAbiTestService,
    OakAbiTestServiceClient, OakAbiTestServiceDispatcher,
};
use rand::Rng;
use std::{collections::HashMap, convert::TryInto};

const BACKEND_COUNT: usize = 3;

const FRONTEND_MODULE_NAME: &str = "frontend_module";
const BACKEND_MODULE_NAME: &str = "backend_module";
const BACKEND_ENTRYPOINT_NAME: &str = "backend_oak_main";
const STORAGE_NAME_PREFIX: &str = "abitest";
const LINEAR_HANDLES_MODULE_NAME: &str = "linear_handles_module";

// Distinct listening addresses to avoid port-in-use errors
const HTTP_ADDR: &str = "[::]:8383";
const ADDITIONAL_TEST_GRPC_SERVER_ADDR: &str = "[::]:8081";
const ADDITIONAL_TEST_HTTP_SERVER_ADDR: &str = "[::]:8082";
const ADDITIONAL_TEST_GRPC_SERVER_ADDR_2: &str = "[::]:8083";
const ADDITIONAL_TEST_HTTP_SERVER_ADDR_2: &str = "[::]:8084";
const ADDITIONAL_TEST_FAIL_SERVER_ADDR: &str = "[::]:8085";

const GRPC_CLIENT_ADDRESS: &str = "https://localhost:7878";
const STORAGE_PROXY_ADDRESS: &str = "https://localhost:7867";
const HTTP_CLIENT_ADDRESS: &str = "https://localhost:7856";

struct FrontendNode {
    backend_out: Vec<oak::WriteHandle>,
    backend_in: Vec<oak::ReadHandle>,
    storage: Option<oak::storage::Storage>,
    absent_storage: Option<oak::storage::Storage>,
    storage_name: Vec<u8>,
    roughtime: Option<oak::roughtime::Roughtime>,
    misconfigured_roughtime: Option<oak::roughtime::Roughtime>,
    crypto: Option<oak::crypto::Crypto>,
}

impl FrontendNode {
    pub fn new() -> Self {
        {
            // Before doing anything else, deliberately lose some channels.
            // We can't check these with automatic testing, but they're useful for
            // manual introspection to check that Runtime internal channel tracking
            // is working correctly.
            //
            // First lose channels directly.
            lose_channels();

            // Second, start an ephemeral Node which also loses channels.
            let (wh, rh) =
                oak::channel_create("channel_loser-initial", &Label::public_untrusted()).unwrap();
            oak::node_create(
                "channel_loser",
                &oak::node_config::wasm(FRONTEND_MODULE_NAME, "channel_loser"),
                &Label::public_untrusted(),
                rh,
            )
            .expect("failed to create channel_loser ephemeral Node");
            oak::channel_close(wh.handle).unwrap();
            oak::channel_close(rh.handle).unwrap();
        }

        {
            // Create a new node to handle HTTP requests
            info!("Starting HTTP server pseudo-node on port {}.", HTTP_ADDR);
            let http_channel = oak::http::server::init(HTTP_ADDR)
                .expect("could not create HTTP server pseudo-Node!");
            oak::node_create(
                "http_oak_main",
                &oak::node_config::wasm(FRONTEND_MODULE_NAME, "http_oak_main"),
                &Label::public_untrusted(),
                http_channel.handle,
            )
            .expect("failed to create http_oak_main Node");
            // Close local handle to the HTTP invocation channel now that it's been passed
            // to the separate HTTP handling node.
            http_channel.close().unwrap();
        }

        let log_sender = oak::logger::create().unwrap();
        oak::logger::init(log_sender, log::Level::Debug).unwrap();

        // Create backend node instances.
        let mut backend_out = Vec::with_capacity(BACKEND_COUNT);
        let mut backend_in = Vec::with_capacity(BACKEND_COUNT);
        for i in 0..BACKEND_COUNT {
            let (write_handle, read_handle) =
                oak::channel_create(&format!("to-backend-{}", i), &Label::public_untrusted())
                    .expect("could not create channel");
            oak::node_create(
                &format!("{}-{}", BACKEND_ENTRYPOINT_NAME, i),
                &oak::node_config::wasm(BACKEND_MODULE_NAME, BACKEND_ENTRYPOINT_NAME),
                &Label::public_untrusted(),
                read_handle,
            )
            .expect("could not create node");
            oak::channel_close(read_handle.handle).expect("could not close channel");
            backend_out.push(write_handle);

            // Create a back channel, and pass the write half to the backend
            // as the first message on the outbound channel.
            let (write_handle, read_handle) =
                oak::channel_create(&format!("from-backend-{}", i), &Label::public_untrusted())
                    .expect("could not create channel");
            oak::channel_write(backend_out[i], &[], &[write_handle.handle])
                .expect("could not write to channel");
            oak::channel_close(write_handle.handle).expect("could not close channel");
            backend_in.push(read_handle);
        }

        // Build a unique storage name, so different test runs don't affect each other.
        let mut nonce = [0; 16];
        oak::random_get(&mut nonce).unwrap();
        let storage_name = format!("{}-{}", STORAGE_NAME_PREFIX, hex::encode(nonce));
        info!("Using storage name '{}' for storage tests", storage_name);

        FrontendNode {
            backend_out,
            backend_in,
            storage: oak::storage::Storage::new(&StorageProxyConfiguration {
                address: STORAGE_PROXY_ADDRESS.to_string(),
            }),
            absent_storage: oak::storage::Storage::new(&StorageProxyConfiguration {
                address: "https://test.invalid:9999".to_string(),
            }),
            storage_name: storage_name.as_bytes().to_vec(),
            roughtime: oak::roughtime::Roughtime::new(&RoughtimeClientConfiguration {
                ..Default::default()
            }),
            misconfigured_roughtime: oak::roughtime::Roughtime::new(
                &RoughtimeClientConfiguration {
                    min_overlapping_intervals: Some(99),
                    ..Default::default()
                },
            ),
            crypto: oak::crypto::Crypto::new(&CryptoConfiguration {}, &Label::public_untrusted()),
        }
    }
}

#[no_mangle]
pub extern "C" fn frontend_oak_main(_in_handle: u64) {
    let _ = std::panic::catch_unwind(|| {
        oak::set_panic_hook();
        let node = FrontendNode::new();
        let grpc_channel =
            oak::grpc::server::init("[::]:8080").expect("could not create gRPC server pseudo-Node");
        oak::run_command_loop(node, grpc_channel.iter());
    });
}

oak::impl_dispatcher!(impl FrontendNode : OakAbiTestServiceDispatcher);

type TestResult = Result<(), Box<dyn std::error::Error>>;
type TestFn = fn(&mut FrontendNode) -> TestResult;

// Expected change in the number of extant Nodes and channels as a result
// of running a test case.
#[derive(PartialEq, Copy, Clone)]
enum Count {
    Unsure,
    Unchanged, // For convenience, equivalent to `Delta {nodes:0, channels:0}`
    Delta { nodes: u32, channels: u32 },
}

impl OakAbiTestService for FrontendNode {
    fn run_tests(&mut self, req: AbiTestRequest) -> grpc::Result<AbiTestResponse> {
        info!(
            "Run tests matching '{}' except those matching '{}'",
            req.include, req.exclude
        );
        if req.predictable_counts {
            info!("Skip tests with unpredictable effects on object counts");
        }
        let include = regex::Regex::new(&req.include).unwrap();
        let exclude = regex::Regex::new(&req.exclude).unwrap();
        let mut results = Vec::<proto::abi_test_response::TestResult>::new();

        // Manual registry of all tests.
        let mut tests: HashMap<&str, (TestFn, Count)> = HashMap::new();
        tests.insert(
            "ChannelCreateRaw",
            (Self::test_channel_create_raw, Count::Unchanged),
        );
        tests.insert(
            "ChannelCreate",
            (Self::test_channel_create, Count::Unchanged),
        );
        tests.insert(
            "ChannelCloseRaw",
            (Self::test_channel_close_raw, Count::Unchanged),
        );
        tests.insert("ChannelClose", (Self::test_channel_close, Count::Unchanged));
        tests.insert(
            "HandleCloneRaw",
            (Self::test_handle_clone_raw, Count::Unchanged),
        );
        tests.insert(
            "LinearHandles",
            (Self::test_linear_handles, Count::Unchanged),
        );
        tests.insert(
            "ChannelReadRaw",
            (Self::test_channel_read_raw, Count::Unchanged),
        );
        tests.insert("ChannelRead", (Self::test_channel_read, Count::Unchanged));
        tests.insert(
            "ChannelReadOrphan",
            (Self::test_channel_read_orphan, Count::Unchanged),
        );
        tests.insert(
            "ChannelReadWithDowngrade",
            (Self::test_channel_read_with_downgrade, Count::Unchanged),
        );
        tests.insert(
            "ChannelWriteRaw",
            (Self::test_channel_write_raw, Count::Unchanged),
        );
        tests.insert("ChannelWrite", (Self::test_channel_write, Count::Unchanged));
        tests.insert(
            "ChannelWriteHandle",
            (Self::test_channel_write_handle, Count::Unchanged),
        );
        tests.insert(
            "ChannelWriteOrphanEmpty",
            (Self::test_channel_write_orphan_empty, Count::Unchanged),
        );
        tests.insert(
            "ChannelWriteOrphanFull",
            (Self::test_channel_write_orphan_full, Count::Unchanged),
        );
        tests.insert(
            "ChannelHandleRecovered",
            (Self::test_channel_handle_recovered, Count::Unchanged),
        );
        tests.insert(
            "ChannelChainLost",
            (Self::test_channel_chain_lost, Count::Unchanged),
        );
        tests.insert(
            "ChannelChainLeaked",
            (
                Self::test_channel_chain_leaked,
                Count::Delta {
                    nodes: 0,
                    channels: 9,
                },
            ),
        );
        tests.insert(
            "ChannelChainRecovered",
            (Self::test_channel_chain_recovered, Count::Unchanged),
        );
        tests.insert(
            "WaitOnChannels",
            (Self::test_channel_wait, Count::Unchanged),
        );
        tests.insert(
            "WaitOnChannelsOrphan",
            (Self::test_channel_wait_orphan, Count::Unchanged),
        );
        tests.insert(
            "WaitOnChannelsWithDowngrade",
            (Self::test_channel_wait_with_downgrade, Count::Unchanged),
        );
        tests.insert(
            "WaitOnChannelsRaw",
            (Self::test_channel_wait_raw, Count::Unchanged),
        );
        tests.insert("NodeCreate", (Self::test_node_create, Count::Unchanged));
        tests.insert(
            "NodeCreateRaw",
            (Self::test_node_create_raw, Count::Unchanged),
        );
        tests.insert(
            "ChannelLabelRead",
            (Self::test_channel_label_read, Count::Unchanged),
        );
        tests.insert(
            "NodeLabelRead",
            (Self::test_node_label_read, Count::Unchanged),
        );
        tests.insert(
            "NodePrivilegeRead",
            (Self::test_node_privilege_read, Count::Unchanged),
        );
        tests.insert(
            "ChannelLabelReadRaw",
            (Self::test_channel_label_read_raw, Count::Unchanged),
        );
        tests.insert(
            "NodeLabelReadRaw",
            (Self::test_node_label_read_raw, Count::Unchanged),
        );
        tests.insert(
            "NodePrivilegeReadRaw",
            (Self::test_node_privilege_read_raw, Count::Unchanged),
        );
        tests.insert("NodePanic", (Self::test_node_panic, Count::Unchanged));
        tests.insert(
            "RandomGetRaw",
            (Self::test_random_get_raw, Count::Unchanged),
        );
        tests.insert("RandomGet", (Self::test_random_get, Count::Unchanged));
        tests.insert("RandomRng", (Self::test_random_rng, Count::Unchanged));
        tests.insert(
            "ChannelHandleReuse",
            (Self::test_channel_handle_reuse, Count::Unchanged),
        );
        tests.insert("Log", (Self::test_log, Count::Unchanged));
        tests.insert("DirectLog", (Self::test_direct_log, Count::Unchanged));
        tests.insert(
            "BackendRoundtrip",
            (Self::test_backend_roundtrip, Count::Unchanged),
        );
        tests.insert("Storage", (Self::test_storage, Count::Unsure));
        tests.insert("AbsentStorage", (Self::test_absent_storage, Count::Unsure));
        tests.insert(
            "GrpcServerSecond",
            (Self::test_grpc_server_second, Count::Unsure),
        );
        tests.insert(
            "GrpcServerInvalidAddress",
            (Self::test_grpc_server_invalid_address, Count::Unchanged),
        );
        tests.insert(
            "GrpcServerFailNoHandle",
            (Self::test_grpc_server_fail_no_handle, Count::Unchanged),
        );
        tests.insert(
            "GrpcServerFailReadHandle",
            (Self::test_grpc_server_fail_read_handle, Count::Unchanged),
        );
        tests.insert(
            "GrpcServerFailTwoHandles",
            (Self::test_grpc_server_fail_two_handles, Count::Unchanged),
        );
        tests.insert(
            "GrpcClientUnaryMethod",
            (Self::test_grpc_client_unary_method, Count::Unsure),
        );
        tests.insert(
            "GrpcClientServerStreamingMethod",
            (
                Self::test_grpc_client_server_streaming_method,
                Count::Unsure,
            ),
        );
        tests.insert(
            "AbsentGrpcClientUnaryMethod",
            (Self::test_absent_grpc_client_unary_method, Count::Unsure),
        );
        tests.insert(
            "AbsentGrpcClientServerStreamingMethod",
            (
                Self::test_absent_grpc_client_server_streaming_method,
                Count::Unsure,
            ),
        );
        tests.insert(
            "HttpServerCreate",
            (Self::test_http_server_create, Count::Unsure),
        );
        tests.insert(
            "HttpServerReservedPort",
            (Self::test_http_server_reserved_port, Count::Unchanged),
        );
        tests.insert(
            "HttpServerInvalidAddress",
            (Self::test_http_server_invalid_address, Count::Unchanged),
        );
        tests.insert(
            "HttpServerFailNoHandle",
            (Self::test_http_server_fail_no_handle, Count::Unchanged),
        );
        tests.insert(
            "HttpServerFailReadHandle",
            (Self::test_http_server_fail_read_handle, Count::Unchanged),
        );
        tests.insert(
            "HttpServerFailTwoHandles",
            (Self::test_http_server_fail_two_handles, Count::Unchanged),
        );
        tests.insert(
            "RoughtimeClient",
            (Self::test_roughtime_client, Count::Unsure),
        );
        tests.insert(
            "MisconfiguredRoughtimeClient",
            (Self::test_roughtime_client_misconfig, Count::Unsure),
        );
        tests.insert("CryptoBind", (Self::test_crypto_bind, Count::Unchanged));
        tests.insert(
            "CryptoFailBind",
            (Self::test_crypto_bind_fail, Count::Unchanged),
        );
        tests.insert("CryptoDAEAD", (Self::test_crypto_daead, Count::Unchanged));
        tests.insert(
            "CryptoFailDAEAD",
            (Self::test_crypto_daead_fail, Count::Unchanged),
        );
        tests.insert("CryptoAEAD", (Self::test_crypto_aead, Count::Unchanged));
        tests.insert(
            "CryptoFailAEAD",
            (Self::test_crypto_aead_fail, Count::Unchanged),
        );
        tests.insert("CryptoMac", (Self::test_crypto_mac, Count::Unchanged));
        tests.insert(
            "CryptoFailMac",
            (Self::test_crypto_mac_fail, Count::Unchanged),
        );
        tests.insert("CryptoPRF", (Self::test_crypto_prf, Count::Unchanged));
        tests.insert(
            "CryptoFailPRF",
            (Self::test_crypto_prf_fail, Count::Unchanged),
        );
        tests.insert(
            "CryptoSignature",
            (Self::test_crypto_sign, Count::Unchanged),
        );
        tests.insert(
            "CryptoFailSignature",
            (Self::test_crypto_sign_fail, Count::Unchanged),
        );
        tests.insert(
            "GrpcServerPseudoNodePrivilege",
            (
                Self::test_grpc_server_pseudo_node_privilege,
                Count::Unchanged,
            ),
        );
        tests.insert(
            "HttpServerPseudoNodePrivilege",
            (
                Self::test_http_server_pseudo_node_privilege,
                Count::Unchanged,
            ),
        );
        tests.insert(
            "GrpcClientPseudoNodePrivilege",
            (
                Self::test_grpc_client_pseudo_node_privilege,
                Count::Unchanged,
            ),
        );
        tests.insert(
            "HttpClientPseudoNodePrivilege",
            (
                Self::test_http_client_pseudo_node_privilege,
                Count::Unchanged,
            ),
        );
        tests.insert(
            "RoughtimeClientPseudoNodePrivilege",
            (
                Self::test_roughtime_client_pseudo_node_privilege,
                Count::Unchanged,
            ),
        );
        tests.insert(
            "StoragePseudoNodePrivilege",
            (Self::test_storage_pseudo_node_privilege, Count::Unchanged),
        );
        tests.insert(
            "LoggerPseudoNodePrivilege",
            (Self::test_logger_pseudo_node_privilege, Count::Unchanged),
        );

        for (&name, &info) in &tests {
            let (testfn, counts) = info;
            if !include.is_match(name) {
                debug!(
                    "skip test '{}' as not included in '{}' include pattern",
                    name, include
                );
                continue;
            }
            if !req.exclude.is_empty() && exclude.is_match(name) {
                debug!(
                    "skip test '{}' as included in '{}' exclude pattern",
                    name, exclude
                );
                continue;
            }
            if req.predictable_counts && counts == Count::Unsure {
                debug!(
                    "skip test '{}' as it has an unpredictable affect on object counts",
                    name,
                );
                continue;
            }
            let mut result = proto::abi_test_response::TestResult {
                name: name.to_string(),
                ..Default::default()
            };
            match counts {
                Count::Unsure => result.predictable_counts = false,
                Count::Unchanged => {
                    result.predictable_counts = true;
                    result.node_change = 0;
                    result.channel_change = 0;
                }
                Count::Delta { nodes, channels } => {
                    result.predictable_counts = true;
                    result.node_change = nodes;
                    result.channel_change = channels;
                }
            };
            if name.starts_with("DISABLED_") {
                debug!("skip test '{}' as marked as disabled", name);
                result.disabled = true;
                result.success = false;
                result.details = "Test disabled".to_string();
                results.push(result);
                continue;
            }
            info!("running test {}", name);
            match testfn(self) {
                Ok(()) => result.success = true,
                Err(err) => {
                    result.success = false;
                    result.details = format!("Error: {}", err);
                }
            }
            results.push(result);
        }

        Ok(AbiTestResponse { results })
    }

    // gRPC test methods.
    fn unary_method(&mut self, req: GrpcTestRequest) -> grpc::Result<GrpcTestResponse> {
        match req.method_result {
            Some(proto::grpc_test_request::MethodResult::ErrCode(err_code)) => {
                info!("unary_method -> Err({})", err_code);
                Err(grpc::build_status(
                    grpc::Code::from_i32(err_code).unwrap(),
                    "Deliberate error",
                ))
            }
            Some(proto::grpc_test_request::MethodResult::OkText(ok_text)) => {
                info!("unary_method -> Ok({})", ok_text);
                let rsp = GrpcTestResponse { text: ok_text };
                Ok(rsp)
            }
            None => panic!("invalid request"),
        }
    }
    fn server_streaming_method(
        &mut self,
        req: GrpcTestRequest,
        writer: grpc::ChannelResponseWriter,
    ) {
        match req.method_result {
            Some(proto::grpc_test_request::MethodResult::ErrCode(err_code)) => {
                info!("server_streaming_method -> Err({})", err_code);
                let status =
                    grpc::build_status(grpc::Code::from_i32(err_code).unwrap(), "Deliberate error");
                writer.close(Err(status)).expect("failed to close writer");
            }
            Some(proto::grpc_test_request::MethodResult::OkText(ok_text)) => {
                // Write two responses to exercise streaming.
                info!("server_streaming_method -> 2 x Ok({})", ok_text);
                let rsp = GrpcTestResponse { text: ok_text };
                writer
                    .write(&rsp, grpc::WriteMode::KeepOpen)
                    .expect("Failed to write response");
                writer
                    .write(&rsp, grpc::WriteMode::Close)
                    .expect("Failed to write response");
            }
            None => panic!("invalid request"),
        };
    }
    fn client_streaming_method(
        &mut self,
        reqs: Vec<GrpcTestRequest>,
    ) -> grpc::Result<GrpcTestResponse> {
        // If any request triggers an error, return it.
        for req in &reqs {
            if let Some(proto::grpc_test_request::MethodResult::ErrCode(err_code)) =
                req.method_result
            {
                info!("client_streaming_method -> Err({})", err_code);
                return Err(grpc::build_status(
                    grpc::Code::from_i32(err_code).unwrap(),
                    "Deliberate error",
                ));
            }
        }
        // Otherwise return the text from all the requests combined.
        let mut combined_text = String::new();
        for req in &reqs {
            if let Some(proto::grpc_test_request::MethodResult::OkText(ok_text)) =
                &req.method_result
            {
                combined_text.push_str(ok_text);
            }
        }
        info!("client_streaming_method -> Ok({})", combined_text);
        Ok(GrpcTestResponse {
            text: combined_text,
        })
    }
    fn bidi_streaming_method(
        &mut self,
        reqs: Vec<GrpcTestRequest>,
        writer: grpc::ChannelResponseWriter,
    ) {
        for req in &reqs {
            match &req.method_result {
                Some(proto::grpc_test_request::MethodResult::ErrCode(err_code)) => {
                    info!("bidi_streaming_method -> Err({})", err_code);
                    let status = grpc::build_status(
                        grpc::Code::from_i32(*err_code).unwrap(),
                        "Deliberate error",
                    );
                    writer.close(Err(status)).expect("failed to close writer");
                }
                Some(proto::grpc_test_request::MethodResult::OkText(ok_text)) => {
                    info!("bidi_streaming_method -> Ok({})", ok_text);
                    let rsp = GrpcTestResponse {
                        text: ok_text.to_string(),
                    };
                    writer
                        .write(&rsp, grpc::WriteMode::KeepOpen)
                        .expect("Failed to write response");
                }
                None => panic!("invalid request"),
            };
        }
    }
}

// Helper for status conversion
fn status_convert<T>(result: Result<T, OakStatus>) -> Result<T, OakError> {
    match result {
        Ok(t) => Ok(t),
        Err(status) => Err(OakError::OakStatus(status)),
    }
}

// Return an offset value that is beyond the bounds of available linear memory.
unsafe fn invalid_raw_offset() -> *mut u64 {
    // Currently no way to get at the `memory.size` Wasm instruction from Rust,
    // so pick a large number instead.
    0x7fff_fff0 as *mut u64
}

// Helper function to simplify creating nodes through oak_abi::channel_create
fn channel_create_raw() -> (u64, u64, u32) {
    let mut w = 0u64;
    let mut r = 0u64;
    let name_bytes = "Raw channel".as_bytes();
    let label_bytes = Label::public_untrusted().serialize();
    let result = unsafe {
        oak_abi::channel_create(
            &mut w as *mut u64,
            &mut r as *mut u64,
            name_bytes.as_ptr(),
            name_bytes.len(),
            label_bytes.as_ptr(),
            label_bytes.len(),
        )
    };
    (w, r, result)
}

impl FrontendNode {
    fn test_channel_create_raw(&mut self) -> TestResult {
        let mut write = 0u64;
        let mut read = 0u64;
        let name_bytes = "Raw channel".as_bytes();
        let label_bytes = Label::public_untrusted().serialize();
        let invalid_string_bytes = vec![240];
        expect_eq!(false, std::str::from_utf8(&invalid_string_bytes).is_ok());

        expect_eq!(OakStatus::ErrInvalidArgs as u32, unsafe {
            oak_abi::channel_create(
                invalid_raw_offset(),
                &mut read as *mut u64,
                name_bytes.as_ptr(),
                name_bytes.len(),
                label_bytes.as_ptr(),
                label_bytes.len(),
            )
        });
        expect_eq!(OakStatus::ErrInvalidArgs as u32, unsafe {
            oak_abi::channel_create(
                &mut write as *mut u64,
                invalid_raw_offset(),
                name_bytes.as_ptr(),
                name_bytes.len(),
                label_bytes.as_ptr(),
                label_bytes.len(),
            )
        });
        expect_eq!(OakStatus::ErrInvalidArgs as u32, unsafe {
            oak_abi::channel_create(
                &mut write as *mut u64,
                &mut read as *mut u64,
                invalid_raw_offset() as *const u8,
                1,
                label_bytes.as_ptr(),
                label_bytes.len(),
            )
        });
        expect_eq!(OakStatus::ErrInvalidArgs as u32, unsafe {
            oak_abi::channel_create(
                &mut write as *mut u64,
                &mut read as *mut u64,
                invalid_string_bytes.as_ptr(),
                invalid_string_bytes.len(),
                label_bytes.as_ptr(),
                label_bytes.len(),
            )
        });
        Ok(())
    }

    fn test_channel_create(&mut self) -> TestResult {
        let mut handles = Vec::<(oak::WriteHandle, oak::ReadHandle)>::new();
        const CHANNEL_COUNT: usize = 50;
        for _ in 0..CHANNEL_COUNT {
            match oak::channel_create("Test", &Label::public_untrusted()) {
                Ok(pair) => handles.push(pair),
                Err(status) => {
                    return Err(Box::new(OakError::OakStatus(status)));
                }
            }
        }
        for (w, r) in handles {
            expect_eq!(Ok(()), oak::channel_close(r.handle));
            expect_eq!(Ok(()), oak::channel_close(w.handle));
        }
        Ok(())
    }

    fn test_channel_close_raw(&mut self) -> TestResult {
        let (w, r, _) = channel_create_raw();

        unsafe {
            expect_eq!(OakStatus::Ok as u32, oak_abi::channel_close(w));
            expect_eq!(OakStatus::Ok as u32, oak_abi::channel_close(r));
            expect_eq!(OakStatus::ErrBadHandle as u32, oak_abi::channel_close(w));
            expect_eq!(
                OakStatus::ErrBadHandle as u32,
                oak_abi::channel_close(9_999_999)
            );
        }
        Ok(())
    }

    fn test_channel_close(&mut self) -> TestResult {
        let (w, r) = oak::channel_create("Test", &Label::public_untrusted()).unwrap();
        expect_eq!(Ok(()), oak::channel_close(w.handle));
        expect_eq!(Ok(()), oak::channel_close(r.handle));
        expect_eq!(Err(OakStatus::ErrBadHandle), oak::channel_close(w.handle));
        expect_eq!(Err(OakStatus::ErrBadHandle), oak::channel_close(9_999_999));

        // Can close ends in either order.
        let (w, r) = oak::channel_create("Test", &Label::public_untrusted()).unwrap();
        expect_eq!(Ok(()), oak::channel_close(r.handle));
        expect_eq!(Ok(()), oak::channel_close(w.handle));
        Ok(())
    }

    fn test_handle_clone_raw(&mut self) -> TestResult {
        let (w, r, _) = channel_create_raw();

        // Clone both handles
        let mut w2 = 0u64;
        let mut r2 = 0u64;
        unsafe {
            expect_eq!(
                OakStatus::Ok as u32,
                oak_abi::handle_clone(w, &mut w2 as *mut u64)
            );
            expect_eq!(
                OakStatus::Ok as u32,
                oak_abi::handle_clone(r, &mut r2 as *mut u64)
            );
        }

        // Handles should be distinct values
        expect!(w != w2);
        expect!(r != r2);

        // Close the original handles
        expect_eq!(Ok(()), oak::channel_close(w));
        expect_eq!(Ok(()), oak::channel_close(r));

        // Check that we can close the cloned handles (and thus the channel remained open after
        // closing the original handles)
        expect_eq!(Ok(()), oak::channel_close(w2));
        expect_eq!(Ok(()), oak::channel_close(r2));

        // Check that an invalid handle cannot be cloned
        let bogus_handle = 99999;
        let mut cloned_bogus_handle = 0u64;
        unsafe {
            expect_eq!(
                OakStatus::ErrBadHandle as u32,
                oak_abi::handle_clone(bogus_handle, &mut cloned_bogus_handle as *mut u64)
            );
        }

        // A handle to a closed channel cannot be cloned
        let (w, r, _) = channel_create_raw();
        expect_eq!(Ok(()), oak::channel_close(w));
        expect_eq!(Ok(()), oak::channel_close(r));
        let closed_handle = r;
        let mut cloned_closed_handle = 0u64;
        unsafe {
            expect_eq!(
                OakStatus::ErrBadHandle as u32,
                oak_abi::handle_clone(closed_handle, &mut cloned_closed_handle as *mut u64)
            );
        }

        // Invalid handle_out parameter returns error
        let (w, r, _) = channel_create_raw();
        unsafe {
            expect_eq!(
                OakStatus::ErrInvalidArgs as u32,
                oak_abi::handle_clone(r, invalid_raw_offset())
            );
        }
        expect_eq!(Ok(()), oak::channel_close(w));
        expect_eq!(Ok(()), oak::channel_close(r));
        Ok(())
    }

    fn test_linear_handles(&mut self) -> TestResult {
        let (init_wh, init_rh) =
            oak::channel_create("linear_handle_init", &Label::public_untrusted()).unwrap();
        // The actual tests run in a separate node, as that code must be compiled with SDK
        // feature 'linear-handles' enabled
        oak::node_create(
            "linear_handles",
            &oak::node_config::wasm(LINEAR_HANDLES_MODULE_NAME, "linear_handles_oak_main"),
            &Label::public_untrusted(),
            init_rh,
        )
        .expect("failed to create linear_handles Node");

        let (result_wh, result_rh) =
            oak::channel_create("linear_handle_result", &Label::public_untrusted()).unwrap();

        // The linear_handles module expects to read a single init message with exactly one handle:
        // a write handle to return the result message in.
        oak::channel_write(init_wh, &[], &[result_wh.handle])
            .expect("Failed to write result handle");

        // The linear_handles module should return a single result message (without handles), its
        // body a string containing "OK".
        let mut buf = Vec::new();
        let mut handles = Vec::new();
        oak::wait_on_channels(&[result_rh]).expect("Channel did not become readable");
        oak::channel_read(result_rh, &mut buf, &mut handles).expect("Failed to read response");
        let msg = String::from_utf8(buf).expect("Response message is not valid UTF8");
        // "OK" if all tests passed, the error message otherwise.
        expect_eq!(msg, "OK");

        expect_eq!(Ok(()), oak::channel_close(init_wh.handle));
        expect_eq!(Ok(()), oak::channel_close(init_rh.handle));
        expect_eq!(Ok(()), oak::channel_close(result_wh.handle));
        expect_eq!(Ok(()), oak::channel_close(result_rh.handle));

        Ok(())
    }

    fn test_channel_read_raw(&mut self) -> TestResult {
        let (out_channel, in_channel, _) = channel_create_raw();

        let mut buf = Vec::<u8>::with_capacity(5);
        let mut handles = Vec::with_capacity(5);
        let mut actual_size: u32 = 99;
        let mut actual_handle_count: u32 = 99;
        unsafe {
            // Try invalid values for the 4 linear memory offset arguments.
            expect_eq!(
                OakStatus::ErrInvalidArgs as u32,
                oak_abi::channel_read(
                    in_channel,
                    invalid_raw_offset() as *mut u8,
                    1,
                    &mut actual_size,
                    handles.as_mut_ptr() as *mut u8,
                    handles.capacity() as u32,
                    &mut actual_handle_count
                )
            );
            expect_eq!(
                OakStatus::ErrInvalidArgs as u32,
                oak_abi::channel_read(
                    in_channel,
                    buf.as_mut_ptr(),
                    buf.capacity(),
                    invalid_raw_offset() as *mut u32,
                    handles.as_mut_ptr() as *mut u8,
                    handles.capacity() as u32,
                    &mut actual_handle_count
                )
            );
            expect_eq!(
                OakStatus::ErrInvalidArgs as u32,
                oak_abi::channel_read(
                    in_channel,
                    buf.as_mut_ptr(),
                    buf.capacity(),
                    &mut actual_size,
                    invalid_raw_offset() as *mut u8,
                    1,
                    &mut actual_handle_count
                )
            );
            expect_eq!(
                OakStatus::ErrInvalidArgs as u32,
                oak_abi::channel_read(
                    in_channel,
                    buf.as_mut_ptr(),
                    buf.capacity(),
                    &mut actual_size,
                    handles.as_mut_ptr() as *mut u8,
                    handles.capacity() as u32,
                    invalid_raw_offset() as *mut u32
                )
            );

            // Valid case.
            expect_eq!(
                OakStatus::ErrChannelEmpty as u32,
                oak_abi::channel_read(
                    in_channel,
                    buf.as_mut_ptr(),
                    buf.capacity(),
                    &mut actual_size,
                    handles.as_mut_ptr() as *mut u8,
                    handles.capacity() as u32,
                    &mut actual_handle_count
                )
            );
            expect_eq!(0, actual_size);
            expect_eq!(0, actual_handle_count);
        }
        expect_eq!(OakStatus::Ok as u32, unsafe {
            oak_abi::channel_close(out_channel)
        });
        expect_eq!(OakStatus::Ok as u32, unsafe {
            oak_abi::channel_close(in_channel)
        });
        Ok(())
    }

    fn test_channel_read(&mut self) -> TestResult {
        let (out_channel, in_channel) =
            oak::channel_create("Test", &Label::public_untrusted()).unwrap();

        // No message pending.
        let mut buffer = Vec::<u8>::with_capacity(5);
        let mut handles = Vec::with_capacity(1);
        expect_eq!(
            Err(OakStatus::ErrChannelEmpty),
            oak::channel_read(in_channel, &mut buffer, &mut handles)
        );
        expect_eq!(0, buffer.len());
        expect_eq!(0, handles.len());

        // No message pending clears any data in input vectors.
        let mut nonempty_buffer = vec![0x91, 0x92, 0x93];
        let mut nonempty_handles = vec![out_channel.handle];
        expect_eq!(
            Err(OakStatus::ErrChannelEmpty),
            oak::channel_read(in_channel, &mut nonempty_buffer, &mut nonempty_handles)
        );
        expect_eq!(0, nonempty_buffer.len());
        expect_eq!(0, nonempty_handles.len());

        // Single message.
        let data = vec![0x01, 0x02, 0x03];
        expect_eq!(Ok(()), oak::channel_write(out_channel, &data, &[]));
        expect_eq!(
            Ok(()),
            oak::channel_read(in_channel, &mut buffer, &mut handles)
        );
        expect_eq!(3, buffer.len());
        expect_eq!(0, handles.len());

        // Reading again zeroes the vector length.
        expect_eq!(
            Err(OakStatus::ErrChannelEmpty),
            oak::channel_read(in_channel, &mut buffer, &mut handles)
        );
        expect_eq!(0, buffer.len());
        expect_eq!(0, handles.len());
        expect_eq!(5, buffer.capacity());

        // Now send and receive a bigger message.
        let data = vec![0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08];
        expect_eq!(Ok(()), oak::channel_write(out_channel, &data, &[]));
        expect_eq!(
            Ok(()),
            oak::channel_read(in_channel, &mut buffer, &mut handles)
        );
        expect_eq!(8, buffer.len());
        expect_eq!(0, handles.len());
        expect!(buffer.capacity() >= 8);

        // Reading from an invalid handle gives an error.
        let bogus_channel = oak::ReadHandle { handle: 99999 };
        expect_eq!(
            Err(OakStatus::ErrBadHandle),
            oak::channel_read(bogus_channel, &mut buffer, &mut handles)
        );

        // Send and receive lots of handles.
        let data = vec![0x01, 0x02, 0x03];
        expect_eq!(
            Ok(()),
            oak::channel_write(
                out_channel,
                &data,
                &[
                    out_channel.handle,
                    out_channel.handle,
                    out_channel.handle,
                    out_channel.handle
                ]
            )
        );
        expect_eq!(
            Ok(()),
            oak::channel_read(in_channel, &mut buffer, &mut handles)
        );
        expect_eq!(3, buffer.len());
        expect_eq!(4, handles.len());
        for handle in &handles {
            oak::channel_close(*handle).expect("could not close channel");
        }

        // Reading again clears the buffer and the handles.
        expect_eq!(
            Err(OakStatus::ErrChannelEmpty),
            oak::channel_read(in_channel, &mut buffer, &mut handles)
        );
        expect_eq!(0, buffer.len());
        expect_eq!(0, handles.len());

        expect_eq!(Ok(()), oak::channel_close(out_channel.handle));
        expect_eq!(Ok(()), oak::channel_close(in_channel.handle));
        Ok(())
    }

    fn test_channel_read_orphan(&mut self) -> TestResult {
        let (out_channel, in_channel) =
            oak::channel_create("Test", &Label::public_untrusted()).unwrap();

        // Write a message to the channel.
        let buf = vec![0x01];
        expect_eq!(Ok(()), oak::channel_write(out_channel, &buf, &[]));

        // Drop the only write handle for this channel.
        expect_eq!(Ok(()), oak::channel_close(out_channel.handle));

        // Channel is not yet read orphaned, because there is a message
        // available.
        let mut buffer = Vec::<u8>::with_capacity(5);
        let mut handles = Vec::with_capacity(5);
        expect_eq!(
            Ok(()),
            oak::channel_read(in_channel, &mut buffer, &mut handles)
        );
        expect_eq!(1, buffer.len());
        expect_eq!(0, handles.len());

        // Now the channel is empty, a second attempt to read fails
        // because the channel is orphaned.
        let mut buffer = Vec::<u8>::with_capacity(5);
        let mut handles = Vec::with_capacity(5);
        expect_eq!(
            Err(OakStatus::ErrChannelClosed),
            oak::channel_read(in_channel, &mut buffer, &mut handles)
        );

        expect_eq!(Ok(()), oak::channel_close(in_channel.handle));
        Ok(())
    }

    fn test_channel_read_with_downgrade(&mut self) -> TestResult {
        let mut buffer = Vec::<u8>::with_capacity(5);
        let test_msg = vec![0x01, 0x02, 0x03];

        let (public_out_channel, public_in_channel) =
            oak::channel_create("Public test channel", &Label::public_untrusted())
                .expect("could not create channel");

        // Test that [`oak::channel_read_with_downgrade`] is successful.
        oak::channel_write(public_out_channel, &test_msg, &[]).expect("could not write to channel");
        expect_eq!(
            Ok(()),
            oak::channel_read_with_downgrade(public_in_channel, &mut buffer, &mut vec![])
        );
        expect_eq!(Ok(()), oak::channel_close(public_out_channel.handle));
        expect_eq!(Ok(()), oak::channel_close(public_in_channel.handle));

        let (private_out_channel, private_in_channel) =
            oak::channel_create("Private test channel", &confidentiality_label(top()))
                .expect("could not create channel");

        // Test that [`oak::channel_read_with_downgrade`] returns
        // [`OakStatus::ErrPermissionDenied`].
        oak::channel_write(private_out_channel, &test_msg, &[])
            .expect("could not write to channel");
        expect_eq!(
            Err(OakStatus::ErrPermissionDenied),
            oak::channel_read_with_downgrade(private_in_channel, &mut buffer, &mut vec![])
        );
        expect_eq!(Ok(()), oak::channel_close(private_out_channel.handle));
        expect_eq!(Ok(()), oak::channel_close(private_in_channel.handle));

        // TODO(#1819): Check the case where results are different from the `channel_read` once the
        // ABI tests can support wasm hash labels.
        Ok(())
    }

    fn test_channel_write_raw(&mut self) -> TestResult {
        let (out_channel, in_channel, _) = channel_create_raw();

        let buf = vec![0x01];
        let handles = vec![in_channel];
        unsafe {
            expect_eq!(
                OakStatus::ErrInvalidArgs as u32,
                oak_abi::channel_write(
                    out_channel,
                    invalid_raw_offset() as *const u8,
                    1,
                    handles.as_ptr() as *const u8,
                    handles.len() as u32,
                )
            );
            expect_eq!(
                OakStatus::ErrInvalidArgs as u32,
                oak_abi::channel_write(
                    out_channel,
                    buf.as_ptr(),
                    buf.len(),
                    invalid_raw_offset() as *const u8,
                    1,
                )
            );
        }
        expect_eq!(OakStatus::Ok as u32, unsafe {
            oak_abi::channel_close(in_channel)
        });
        expect_eq!(OakStatus::Ok as u32, unsafe {
            oak_abi::channel_close(out_channel)
        });
        Ok(())
    }

    fn test_channel_write(&mut self) -> TestResult {
        let (out_channel, in_channel) =
            oak::channel_create("Test", &Label::public_untrusted()).unwrap();

        // Empty message.
        let empty = vec![];
        expect_eq!(Ok(()), oak::channel_write(out_channel, &empty, &[]));

        // Single message.
        let data = vec![0x01, 0x02, 0x03];
        expect_eq!(Ok(()), oak::channel_write(out_channel, &data, &[]));

        // Now send a bigger message.
        let data = vec![0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08];
        expect_eq!(Ok(()), oak::channel_write(out_channel, &data, &[]));

        // Writing to an invalid handle gives an error.
        let bogus_channel = oak::WriteHandle { handle: 99999 };
        expect_eq!(
            Err(OakStatus::ErrBadHandle),
            oak::channel_write(bogus_channel, &data, &[])
        );

        expect_eq!(Ok(()), oak::channel_close(in_channel.handle));
        expect_eq!(Ok(()), oak::channel_close(out_channel.handle));
        Ok(())
    }

    fn test_channel_write_handle(&mut self) -> TestResult {
        let (out_channel, in_channel) =
            oak::channel_create("Test", &Label::public_untrusted()).unwrap();

        // Send a single handle.
        let empty = vec![];
        expect_eq!(
            Ok(()),
            oak::channel_write(out_channel, &empty, &[in_channel.handle])
        );

        let mut buffer = Vec::<u8>::with_capacity(5);
        let mut handles = Vec::with_capacity(1);
        expect_eq!(
            Ok(()),
            oak::channel_read(in_channel, &mut buffer, &mut handles)
        );
        expect_eq!(0, buffer.len());
        expect_eq!(1, handles.len());
        // The transferred handle has a new value.
        expect!(handles[0] != in_channel.handle);

        expect_eq!(Ok(()), oak::channel_close(handles[0]));
        expect_eq!(Ok(()), oak::channel_close(in_channel.handle));
        expect_eq!(Ok(()), oak::channel_close(out_channel.handle));
        Ok(())
    }

    fn test_channel_write_orphan_empty(&mut self) -> TestResult {
        let (out_channel, in_channel) =
            oak::channel_create("Test", &Label::public_untrusted()).unwrap();

        // Close the only read handle for the channel.
        expect_eq!(Ok(()), oak::channel_close(in_channel.handle));

        // There's no way to read from the channel, so writing fails.
        let data = vec![0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08];
        expect_eq!(
            Err(OakStatus::ErrChannelClosed),
            oak::channel_write(out_channel, &data, &[])
        );
        expect_eq!(Ok(()), oak::channel_close(out_channel.handle));

        Ok(())
    }

    fn test_channel_write_orphan_full(&mut self) -> TestResult {
        let (out_channel, in_channel) =
            oak::channel_create("Test", &Label::public_untrusted()).unwrap();

        // Ensure that there are messages pending on the channel.
        let data = vec![0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08];
        expect_eq!(Ok(()), oak::channel_write(out_channel, &data, &[]));
        expect_eq!(Ok(()), oak::channel_write(out_channel, &data, &[]));
        expect_eq!(Ok(()), oak::channel_write(out_channel, &data, &[]));

        // Once there's no way to read from the channel, writing fails.
        expect_eq!(Ok(()), oak::channel_close(in_channel.handle));
        expect_eq!(
            Err(OakStatus::ErrChannelClosed),
            oak::channel_write(out_channel, &data, &[])
        );
        expect_eq!(Ok(()), oak::channel_close(out_channel.handle));
        Ok(())
    }

    fn test_channel_handle_recovered(&mut self) -> TestResult {
        // Set up a channel with a message in it.
        let (lost_wh, lost_rh) = oak::channel_create("Test", &Label::public_untrusted()).unwrap();
        let data = vec![0x08, 0x0c];
        expect_eq!(Ok(()), oak::channel_write(lost_wh, &data, &[]));

        // Put a message with handle to the first channel into a second channel.
        let (holder_wh, holder_rh) =
            oak::channel_create("Test", &Label::public_untrusted()).unwrap();
        expect_eq!(
            Ok(()),
            oak::channel_write(holder_wh, &[], &[lost_rh.handle])
        );
        expect_eq!(Ok(()), oak::channel_close(holder_wh.handle));

        // Close both handles for the first channel.  At this point the only reference
        // to the first channel is inside the message that's pending on the second channel.
        expect_eq!(Ok(()), oak::channel_close(lost_wh.handle));
        expect_eq!(Ok(()), oak::channel_close(lost_rh.handle));

        // Now pull a handle for the first channel out of the second channel,
        // much like a magician pulling a rabbit from a hat.
        let mut buffer = Vec::<u8>::with_capacity(5);
        let mut handles = Vec::with_capacity(1);
        expect_eq!(
            Ok(()),
            oak::channel_read(holder_rh, &mut buffer, &mut handles)
        );
        expect_eq!(0, buffer.len());
        expect_eq!(1, handles.len());
        let recovered_rh = handles[0];

        // And was your card the eight of clubs?
        expect_eq!(
            Ok(()),
            oak::channel_read(
                oak::ReadHandle {
                    handle: recovered_rh
                },
                &mut buffer,
                &mut handles
            )
        );
        expect_eq!(0, handles.len());
        expect_eq!(2, buffer.len());
        expect_eq!(8, buffer[0]);
        expect_eq!(0xC, buffer[1]);

        expect_eq!(Ok(()), oak::channel_close(recovered_rh));
        expect_eq!(Ok(()), oak::channel_close(holder_rh.handle));
        Ok(())
    }

    fn test_channel_chain_lost(&mut self) -> TestResult {
        let outermost_rh = new_channel_chain(8)?;
        // Close the outermost read handle.  This should lead to a cascade of
        // channel deletion inside the Runtime as the only references to inner
        // channels get removed in turn.
        expect_eq!(Ok(()), oak::channel_close(outermost_rh.handle));
        Ok(())
    }

    fn test_channel_chain_leaked(&mut self) -> TestResult {
        let outermost_rh = new_channel_chain(8)?;
        info!("Deliberately forgetting handle value {:?}", outermost_rh);
        Ok(())
    }

    fn test_channel_chain_recovered(&mut self) -> TestResult {
        let nest_count = 8;
        let outermost_rh = new_channel_chain(nest_count)?;
        let mut outer_rh = outermost_rh;
        for _ in 0..nest_count {
            // Expect to read a message with a single handle from the current outer handle.
            let mut buffer = Vec::<u8>::with_capacity(5);
            let mut handles = Vec::with_capacity(1);
            expect_eq!(
                Ok(()),
                oak::channel_read(outer_rh, &mut buffer, &mut handles)
            );
            expect_eq!(0, buffer.len());
            expect_eq!(1, handles.len());
            let inner_rh = handles[0];
            expect_eq!(Ok(()), oak::channel_close(outer_rh.handle));
            outer_rh = oak::ReadHandle { handle: inner_rh };
        }
        let innermost_rh = outer_rh;

        let mut buffer = Vec::<u8>::with_capacity(5);
        let mut handles = Vec::with_capacity(1);
        expect_eq!(
            Ok(()),
            oak::channel_read(innermost_rh, &mut buffer, &mut handles)
        );
        expect_eq!(0, handles.len());
        expect_eq!(2, buffer.len());
        expect_eq!(8, buffer[0]);
        expect_eq!(0xC, buffer[1]);

        expect_eq!(Ok(()), oak::channel_close(innermost_rh.handle));
        Ok(())
    }

    fn test_channel_wait_raw(&mut self) -> TestResult {
        let (out_channel, in_channel, _) = channel_create_raw();
        let (out_empty_channel, in_empty_channel, _) = channel_create_raw();

        unsafe {
            // Write a message to the channel so wait operations don't block.
            let data = vec![0x01, 0x02, 0x03];
            expect_eq!(
                OakStatus::Ok as u32,
                oak_abi::channel_write(out_channel, data.as_ptr(), data.len(), &[] as *const u8, 0)
            );

            expect_eq!(
                OakStatus::ErrInvalidArgs as u32,
                oak_abi::wait_on_channels(invalid_raw_offset() as *mut u8, 1)
            );
        }

        unsafe {
            // Wait on [write handle, ready read handle, not-ready read handle].
            const COUNT: usize = 3;
            let mut space = Vec::with_capacity(COUNT * oak_abi::SPACE_BYTES_PER_HANDLE);
            space
                .write_u64::<byteorder::LittleEndian>(out_channel)
                .unwrap();
            space.push(0x00);
            space
                .write_u64::<byteorder::LittleEndian>(in_channel)
                .unwrap();
            space.push(0x00);
            space
                .write_u64::<byteorder::LittleEndian>(in_empty_channel)
                .unwrap();
            space.push(0x00);

            expect_eq!(
                OakStatus::Ok as u32,
                oak_abi::wait_on_channels(space.as_mut_ptr(), COUNT as u32)
            );
            expect_eq!(
                ChannelReadStatus::InvalidChannel as i32,
                i32::from(space[8])
            );
            expect_eq!(ChannelReadStatus::ReadReady as i32, i32::from(space[9 + 8]));
            expect_eq!(
                ChannelReadStatus::NotReady as i32,
                i32::from(space[9 + 9 + 8])
            );
        }

        unsafe {
            // Wait on [nonsense handle, read handle].
            const COUNT: usize = 2;
            let mut space = Vec::with_capacity(COUNT * oak_abi::SPACE_BYTES_PER_HANDLE);
            space
                .write_u64::<byteorder::LittleEndian>(9_123_456)
                .unwrap();
            space.push(0x00);
            space
                .write_u64::<byteorder::LittleEndian>(in_channel)
                .unwrap();
            space.push(0x00);
            expect_eq!(
                OakStatus::Ok as u32,
                oak_abi::wait_on_channels(space.as_mut_ptr(), COUNT as u32)
            );
            expect_eq!(
                ChannelReadStatus::InvalidChannel as i32,
                i32::from(space[8])
            );
            expect_eq!(ChannelReadStatus::ReadReady as i32, i32::from(space[9 + 8]));
            expect_eq!(OakStatus::Ok as u32, oak_abi::channel_close(out_channel));
        }

        // Still a pending message on in_channel even though the only write half for
        // the channel is closed.
        unsafe {
            const COUNT: usize = 1;
            let mut space = Vec::with_capacity(COUNT * oak_abi::SPACE_BYTES_PER_HANDLE);
            space
                .write_u64::<byteorder::LittleEndian>(in_channel)
                .unwrap();
            space.push(0x00);
            expect_eq!(
                OakStatus::Ok as u32,
                oak_abi::wait_on_channels(space.as_mut_ptr(), COUNT as u32)
            );
            expect_eq!(ChannelReadStatus::ReadReady as i32, i32::from(space[8]));
        }
        // Consume the pending message.
        let mut buffer = Vec::with_capacity(5);
        let mut recv_len = 0u32;
        let mut handles = Vec::with_capacity(5);
        let mut recv_handles = 0u32;
        unsafe {
            expect_eq!(
                OakStatus::Ok as u32,
                oak_abi::channel_read(
                    in_channel,
                    buffer.as_mut_ptr() as *mut u8,
                    buffer.capacity(),
                    &mut recv_len,
                    handles.as_mut_ptr() as *mut u8,
                    handles.capacity() as u32,
                    &mut recv_handles
                )
            );
        }
        expect_eq!(3, recv_len);
        expect_eq!(0, recv_handles);

        // Read half is now orphaned (no pending message, no possible writers).
        unsafe {
            const COUNT: usize = 1;
            let mut space = Vec::with_capacity(COUNT * oak_abi::SPACE_BYTES_PER_HANDLE);
            space
                .write_u64::<byteorder::LittleEndian>(in_channel)
                .unwrap();
            space.push(0x00);
            expect_eq!(
                OakStatus::Ok as u32,
                oak_abi::wait_on_channels(space.as_mut_ptr(), COUNT as u32)
            );
            expect_eq!(ChannelReadStatus::Orphaned as i32, i32::from(space[8]));

            expect_eq!(OakStatus::Ok as u32, oak_abi::channel_close(in_channel));
        }

        unsafe {
            expect_eq!(
                OakStatus::Ok as u32,
                oak_abi::channel_close(in_empty_channel)
            );
            expect_eq!(
                OakStatus::Ok as u32,
                oak_abi::channel_close(out_empty_channel)
            );
        }

        Ok(())
    }

    fn test_channel_wait(&mut self) -> TestResult {
        let (out1, in1) = oak::channel_create("Test", &Label::public_untrusted()).unwrap();
        let (out2, in2) = oak::channel_create("Test", &Label::public_untrusted()).unwrap();

        // Waiting on (just) non-read channel handles should fail immediately.
        expect_eq!(
            vec![
                ChannelReadStatus::InvalidChannel,
                ChannelReadStatus::InvalidChannel
            ],
            status_convert(oak::wait_on_channels(&[
                oak::ReadHandle {
                    handle: out1.handle
                },
                oak::ReadHandle { handle: 9_999_999 }
            ]))?
        );

        // Set up first channel with a pending message.
        let data = vec![0x01, 0x02, 0x03];
        expect_eq!(Ok(()), oak::channel_write(out1, &data, &[]));

        expect_eq!(
            vec![ChannelReadStatus::ReadReady, ChannelReadStatus::NotReady],
            status_convert(oak::wait_on_channels(&[in1, in2]))?
        );
        // No read so still ready (level triggered not edge triggered).
        expect_eq!(
            vec![ChannelReadStatus::ReadReady, ChannelReadStatus::NotReady],
            status_convert(oak::wait_on_channels(&[in1, in2]))?
        );

        expect_eq!(Ok(()), oak::channel_write(out2, &data, &[]));
        expect_eq!(
            vec![ChannelReadStatus::ReadReady, ChannelReadStatus::ReadReady],
            status_convert(oak::wait_on_channels(&[in1, in2]))?
        );

        let mut buffer = Vec::<u8>::with_capacity(5);
        let mut handles = Vec::with_capacity(5);
        expect_eq!(Ok(()), oak::channel_read(in1, &mut buffer, &mut handles));
        expect_eq!(3, buffer.len());
        expect_eq!(0, handles.len());

        expect_eq!(
            vec![ChannelReadStatus::NotReady, ChannelReadStatus::ReadReady],
            status_convert(oak::wait_on_channels(&[in1, in2]))?
        );

        // Write channels and nonsense handles are ignored.
        expect_eq!(
            vec![
                ChannelReadStatus::NotReady,
                ChannelReadStatus::ReadReady,
                ChannelReadStatus::InvalidChannel
            ],
            status_convert(oak::wait_on_channels(&[
                in1,
                in2,
                oak::ReadHandle {
                    handle: out1.handle
                }
            ]))?
        );
        expect_eq!(
            vec![
                ChannelReadStatus::NotReady,
                ChannelReadStatus::ReadReady,
                ChannelReadStatus::InvalidChannel
            ],
            status_convert(oak::wait_on_channels(&[
                in1,
                in2,
                oak::ReadHandle { handle: 9_999_999 }
            ]))?
        );

        expect_eq!(Ok(()), oak::channel_close(out1.handle));
        expect_eq!(Ok(()), oak::channel_close(out2.handle));

        // Still a pending message on in2 even though the only write half for
        // the channel is closed.
        expect_eq!(
            vec![ChannelReadStatus::ReadReady],
            status_convert(oak::wait_on_channels(&[in2]))?
        );

        expect_eq!(Ok(()), oak::channel_close(in1.handle));
        expect_eq!(Ok(()), oak::channel_close(in2.handle));
        Ok(())
    }

    fn test_channel_wait_orphan(&mut self) -> TestResult {
        // Use 2 channels so there's always a ready channel to prevent
        // wait_on_channels blocking.
        let (out1, in1) = oak::channel_create("Test", &Label::public_untrusted()).unwrap();
        let (out2, in2) = oak::channel_create("Test", &Label::public_untrusted()).unwrap();

        // Set up pending messages so each channel is read-ready.
        let data = vec![0x01, 0x02, 0x03];
        expect_eq!(Ok(()), oak::channel_write(out1, &data, &[]));
        expect_eq!(Ok(()), oak::channel_write(out2, &data, &[]));
        expect_eq!(
            vec![ChannelReadStatus::ReadReady, ChannelReadStatus::ReadReady],
            status_convert(oak::wait_on_channels(&[in1, in2]))?
        );

        // Close the only write handle to channel 1.
        expect_eq!(Ok(()), oak::channel_close(out1.handle));

        // Channel is still read-ready because there's a queued message.
        expect_eq!(
            vec![ChannelReadStatus::ReadReady],
            status_convert(oak::wait_on_channels(&[in1]))?
        );

        // Consume the only message on channel 1.
        let mut buffer = Vec::<u8>::with_capacity(5);
        let mut handles = Vec::with_capacity(5);
        expect_eq!(Ok(()), oak::channel_read(in1, &mut buffer, &mut handles));
        expect_eq!(3, buffer.len());
        expect_eq!(0, handles.len());

        // Now expect the channel status to be orphaned.
        expect_eq!(
            vec![ChannelReadStatus::Orphaned, ChannelReadStatus::ReadReady],
            status_convert(oak::wait_on_channels(&[in1, in2]))?
        );

        expect_eq!(Ok(()), oak::channel_close(in1.handle));
        expect_eq!(Ok(()), oak::channel_close(in2.handle));
        expect_eq!(Ok(()), oak::channel_close(out2.handle));
        Ok(())
    }

    fn test_channel_wait_with_downgrade(&mut self) -> TestResult {
        let test_msg = vec![0x01, 0x02, 0x03];

        let (public_out_channel, public_in_channel) =
            oak::channel_create("Public test channel", &Label::public_untrusted())
                .expect("could not create channel");

        // Test that [`oak::wait_on_channels_with_downgrade`] is successful and returns
        // [`ChannelReadStatus::ReadReady`].
        oak::channel_write(public_out_channel, &test_msg, &[]).expect("could not write to channel");
        expect_eq!(
            vec![ChannelReadStatus::ReadReady],
            status_convert(oak::wait_on_channels_with_downgrade(&[public_in_channel]))?
        );
        expect_eq!(Ok(()), oak::channel_close(public_out_channel.handle));
        expect_eq!(Ok(()), oak::channel_close(public_in_channel.handle));

        let (private_out_channel, private_in_channel) =
            oak::channel_create("Private test channel", &confidentiality_label(top()))
                .expect("could not create channel");

        // Test that [`oak::wait_on_channels_with_downgrade`] returns
        // [`ChannelReadStatus::PermissionDenied`].
        oak::channel_write(private_out_channel, &test_msg, &[])
            .expect("could not write to channel");
        expect_eq!(
            vec![ChannelReadStatus::PermissionDenied],
            status_convert(oak::wait_on_channels_with_downgrade(&[private_in_channel]))?
        );
        expect_eq!(Ok(()), oak::channel_close(private_out_channel.handle));
        expect_eq!(Ok(()), oak::channel_close(private_in_channel.handle));

        // TODO(#1819): Check the case where results are different from the `wait_on_channels` once
        // the ABI tests can support wasm hash labels.
        Ok(())
    }

    fn test_node_create_raw(&mut self) -> TestResult {
        let (out_handle, in_handle, _) = channel_create_raw();

        let valid_label_bytes = Label::public_untrusted().serialize();
        let name_bytes = "Raw node".as_bytes();

        // This sequence of bytes should not deserialize as a [`oak_abi::proto::label::Label`]
        // or [`oak_abi::proto::oak::application::NodeConfiguration`] protobuf. We make
        // sure here that this continues to be the case by making sure that
        // [`Label::decode`] and [`NodeConfiguration::decode`] fail to parse these bytes.
        let invalid_proto_bytes = vec![0, 88, 0];
        assert!(Label::decode(invalid_proto_bytes.as_ref()).is_err());
        assert!(NodeConfiguration::decode(invalid_proto_bytes.as_ref()).is_err());

        // This is not a valid UTF-8 encoding.
        let invalid_string_bytes = vec![240];
        assert!(std::str::from_utf8(invalid_string_bytes.as_ref()).is_err());

        {
            let mut config_bytes = Vec::new();
            oak::node_config::wasm(BACKEND_MODULE_NAME, BACKEND_ENTRYPOINT_NAME)
                .encode(&mut config_bytes)?;
            expect_eq!(OakStatus::Ok as u32, unsafe {
                oak_abi::node_create(
                    name_bytes.as_ptr(),
                    name_bytes.len(),
                    config_bytes.as_ptr(),
                    config_bytes.len(),
                    valid_label_bytes.as_ptr(),
                    valid_label_bytes.len(),
                    in_handle,
                )
            });
        }

        {
            let mut config_bytes = Vec::new();
            oak::node_config::wasm(BACKEND_MODULE_NAME, BACKEND_ENTRYPOINT_NAME)
                .encode(&mut config_bytes)?;
            expect_eq!(OakStatus::ErrInvalidArgs as u32, unsafe {
                oak_abi::node_create(
                    invalid_string_bytes.as_ptr(),
                    invalid_string_bytes.len(),
                    config_bytes.as_ptr(),
                    config_bytes.len(),
                    valid_label_bytes.as_ptr(),
                    valid_label_bytes.len(),
                    in_handle,
                )
            });
        }

        {
            let mut config_bytes = Vec::new();
            oak::node_config::wasm(BACKEND_MODULE_NAME, BACKEND_ENTRYPOINT_NAME)
                .encode(&mut config_bytes)?;
            expect_eq!(OakStatus::ErrInvalidArgs as u32, unsafe {
                oak_abi::node_create(
                    invalid_raw_offset() as *const u8,
                    1,
                    config_bytes.as_ptr(),
                    config_bytes.len(),
                    valid_label_bytes.as_ptr(),
                    valid_label_bytes.len(),
                    in_handle,
                )
            });
        }

        {
            let mut config_bytes = Vec::new();
            oak::node_config::wasm(BACKEND_MODULE_NAME, BACKEND_ENTRYPOINT_NAME)
                .encode(&mut config_bytes)?;
            expect_eq!(OakStatus::ErrInvalidArgs as u32, unsafe {
                oak_abi::node_create(
                    name_bytes.as_ptr(),
                    name_bytes.len(),
                    config_bytes.as_ptr(),
                    config_bytes.len(),
                    invalid_raw_offset() as *const u8,
                    1,
                    in_handle,
                )
            });
        }

        {
            let mut config_bytes = Vec::new();
            oak::node_config::wasm(BACKEND_MODULE_NAME, BACKEND_ENTRYPOINT_NAME)
                .encode(&mut config_bytes)?;
            expect_eq!(OakStatus::ErrInvalidArgs as u32, unsafe {
                oak_abi::node_create(
                    name_bytes.as_ptr(),
                    name_bytes.len(),
                    config_bytes.as_ptr(),
                    config_bytes.len(),
                    invalid_proto_bytes.as_ptr(),
                    invalid_proto_bytes.len(),
                    in_handle,
                )
            });
        }

        {
            expect_eq!(OakStatus::ErrInvalidArgs as u32, unsafe {
                oak_abi::node_create(
                    name_bytes.as_ptr(),
                    name_bytes.len(),
                    invalid_raw_offset() as *const u8,
                    1,
                    valid_label_bytes.as_ptr(),
                    valid_label_bytes.len(),
                    in_handle,
                )
            });
        }

        {
            expect_eq!(OakStatus::ErrInvalidArgs as u32, unsafe {
                oak_abi::node_create(
                    name_bytes.as_ptr(),
                    name_bytes.len(),
                    invalid_proto_bytes.as_ptr(),
                    invalid_proto_bytes.len(),
                    valid_label_bytes.as_ptr(),
                    valid_label_bytes.len(),
                    in_handle,
                )
            });
        }

        expect_eq!(Ok(()), oak::channel_close(in_handle));
        expect_eq!(Ok(()), oak::channel_close(out_handle));
        Ok(())
    }
    fn test_node_create(&mut self) -> TestResult {
        expect_eq!(
            Err(OakStatus::ErrInvalidArgs),
            oak::node_create(
                "Non-existent",
                &oak::node_config::wasm("no_such_module", BACKEND_ENTRYPOINT_NAME),
                &Label::public_untrusted(),
                self.backend_in[0]
            )
        );
        expect_eq!(
            Err(OakStatus::ErrInvalidArgs),
            oak::node_create(
                "No entrypoint",
                &oak::node_config::wasm(BACKEND_MODULE_NAME, "no_such_entrypoint"),
                &Label::public_untrusted(),
                self.backend_in[0]
            )
        );
        expect_eq!(
            Err(OakStatus::ErrInvalidArgs),
            oak::node_create(
                "Invalid signature",
                &oak::node_config::wasm(
                    BACKEND_MODULE_NAME,
                    "backend_fake_main" /* exists but wrong signature */
                ),
                &Label::public_untrusted(),
                self.backend_in[0]
            )
        );
        expect_eq!(
            Err(OakStatus::ErrBadHandle),
            oak::node_create(
                "Invalid handle",
                &oak::node_config::wasm(BACKEND_MODULE_NAME, BACKEND_ENTRYPOINT_NAME),
                &Label::public_untrusted(),
                oak::ReadHandle {
                    handle: oak_abi::INVALID_HANDLE
                }
            )
        );
        let (out_handle, in_handle) =
            oak::channel_create("Test", &Label::public_untrusted()).unwrap();
        expect_eq!(
            Ok(()),
            oak::node_create(
                "Valid",
                &oak::node_config::wasm(BACKEND_MODULE_NAME, BACKEND_ENTRYPOINT_NAME),
                &Label::public_untrusted(),
                in_handle
            )
        );
        expect_eq!(
            Ok(()),
            oak::node_create(
                "Valid2",
                &oak::node_config::wasm(BACKEND_MODULE_NAME, BACKEND_ENTRYPOINT_NAME),
                &Label::public_untrusted(),
                in_handle
            )
        );

        expect_eq!(Ok(()), oak::channel_close(in_handle.handle));
        expect_eq!(Ok(()), oak::channel_close(out_handle.handle));
        Ok(())
    }

    fn test_channel_label_read(&mut self) -> TestResult {
        let hash = vec![1, 2, 3, 4];
        let label = Label {
            confidentiality_tags: vec![oak_abi::label::web_assembly_module_tag(&hash)],
            integrity_tags: vec![],
        };

        // Expect valid handles to return correct label.
        let (out_handle, in_handle) = oak::channel_create("Test", &label).unwrap();
        let expected = Ok(label);
        expect_eq!(expected, oak::channel_label_read(in_handle.handle));
        expect_eq!(expected, oak::channel_label_read(out_handle.handle));

        // Reading the label from an invalid handle gives an error.
        expect_eq!(Err(OakStatus::ErrBadHandle), oak::channel_label_read(99999));

        expect_eq!(Ok(()), oak::channel_close(in_handle.handle));
        expect_eq!(Ok(()), oak::channel_close(out_handle.handle));
        Ok(())
    }

    fn test_node_label_read(&mut self) -> TestResult {
        let expected = Ok(Label::public_untrusted());
        expect_eq!(expected, oak::node_label_read());
        Ok(())
    }

    fn test_node_privilege_read(&mut self) -> TestResult {
        let privilege = oak::node_privilege_read();
        expect_matches!(privilege, Ok(_));
        let confidentiality_tags = privilege.unwrap().confidentiality_tags.to_vec();
        expect_eq!(1, confidentiality_tags.len());
        let tag = confidentiality_tags[0].tag.clone().unwrap();
        expect_matches!(
            tag,
            oak_abi::proto::oak::label::tag::Tag::WebAssemblyModuleTag(_)
        );
        match tag {
            oak_abi::proto::oak::label::tag::Tag::WebAssemblyModuleTag(module_tag) => {
                expect_eq!(32, module_tag.web_assembly_module_hash_sha_256.len())
            }
            _ => {
                error!("Unreachable code reached.");
                unreachable!();
            }
        };
        Ok(())
    }

    fn test_channel_label_read_raw(&mut self) -> TestResult {
        let (out_channel, in_channel, _) = channel_create_raw();

        let mut buf = Vec::<u8>::with_capacity(5);
        let mut actual_size: u32 = 99;
        unsafe {
            // Try invalid values for the 2 linear memory offset arguments.
            expect_eq!(
                OakStatus::ErrInvalidArgs as u32,
                oak_abi::channel_label_read(
                    in_channel,
                    invalid_raw_offset() as *mut u8,
                    1,
                    &mut actual_size
                )
            );
            expect_eq!(
                OakStatus::ErrInvalidArgs as u32,
                oak_abi::channel_label_read(
                    in_channel,
                    buf.as_mut_ptr(),
                    buf.capacity(),
                    invalid_raw_offset() as *mut u32
                )
            );

            // Valid case.
            expect_eq!(
                OakStatus::Ok as u32,
                oak_abi::channel_label_read(
                    in_channel,
                    buf.as_mut_ptr(),
                    buf.capacity(),
                    &mut actual_size
                )
            );
            // Public untrusted label has 0 size.
            expect_eq!(0, actual_size);
        }

        expect_eq!(OakStatus::Ok as u32, unsafe {
            oak_abi::channel_close(out_channel)
        });
        expect_eq!(OakStatus::Ok as u32, unsafe {
            oak_abi::channel_close(in_channel)
        });
        Ok(())
    }

    fn test_node_label_read_raw(&mut self) -> TestResult {
        let mut buf = Vec::<u8>::with_capacity(5);
        let mut actual_size: u32 = 99;
        unsafe {
            // Try invalid values for the 2 linear memory offset arguments.
            expect_eq!(
                OakStatus::ErrInvalidArgs as u32,
                oak_abi::node_label_read(invalid_raw_offset() as *mut u8, 1, &mut actual_size)
            );
            expect_eq!(
                OakStatus::ErrInvalidArgs as u32,
                oak_abi::node_label_read(
                    buf.as_mut_ptr(),
                    buf.capacity(),
                    invalid_raw_offset() as *mut u32
                )
            );

            // Valid case.
            expect_eq!(
                OakStatus::Ok as u32,
                oak_abi::node_label_read(buf.as_mut_ptr(), buf.capacity(), &mut actual_size)
            );
            // Public untrusted label has 0 size.
            expect_eq!(0, actual_size);
        }
        Ok(())
    }

    fn test_node_privilege_read_raw(&mut self) -> TestResult {
        let mut buf = Vec::<u8>::with_capacity(5);
        let mut actual_size: u32 = 99;
        unsafe {
            // Try invalid values for the 2 linear memory offset arguments.
            expect_eq!(
                OakStatus::ErrInvalidArgs as u32,
                oak_abi::node_privilege_read(invalid_raw_offset() as *mut u8, 1, &mut actual_size)
            );
            expect_eq!(
                OakStatus::ErrInvalidArgs as u32,
                oak_abi::node_privilege_read(
                    buf.as_mut_ptr(),
                    buf.capacity(),
                    invalid_raw_offset() as *mut u32
                )
            );

            // Buffer too small.
            expect_eq!(
                OakStatus::ErrBufferTooSmall as u32,
                oak_abi::node_privilege_read(buf.as_mut_ptr(), buf.capacity(), &mut actual_size)
            );

            // Valid case.
            buf.reserve(100);
            expect_eq!(
                OakStatus::Ok as u32,
                oak_abi::node_privilege_read(buf.as_mut_ptr(), buf.capacity(), &mut actual_size)
            );
            // Should be a valid encoding of a privilege label containing two
            // `WebAssemblyModuleTag`s, each containing a SHA256 (32 byte) hash.
            let hash = [0; 32];
            let label = Label {
                confidentiality_tags: vec![oak_abi::label::web_assembly_module_tag(&hash)],
                integrity_tags: vec![oak_abi::label::web_assembly_module_tag(&hash)],
            };
            expect_eq!(label.encoded_len() as u32, actual_size);
        }
        Ok(())
    }

    fn test_node_panic(&mut self) -> TestResult {
        let (out_handle, in_handle) =
            oak::channel_create("Test", &Label::public_untrusted()).unwrap();
        // Create a Node that panics. We can't see the panic, but the rest
        // of the Application should continue.
        expect_eq!(
            Ok(()),
            oak::node_create(
                "panic_main",
                &oak::node_config::wasm(FRONTEND_MODULE_NAME, "panic_main"),
                &Label::public_untrusted(),
                in_handle
            )
        );

        expect_eq!(Ok(()), oak::channel_close(in_handle.handle));
        expect_eq!(Ok(()), oak::channel_close(out_handle.handle));
        Ok(())
    }

    fn test_random_get_raw(&mut self) -> TestResult {
        unsafe {
            expect_eq!(
                OakStatus::ErrInvalidArgs as u32,
                oak_abi::random_get(invalid_raw_offset() as *mut u8, 1)
            );
        }
        Ok(())
    }

    fn test_random_get(&mut self) -> TestResult {
        let original = vec![0x01, 0x02, 0x03, 0x04];
        let mut data = original.clone();
        expect_eq!(Ok(()), oak::random_get(&mut data));
        // 1 in 2^32 chance of getting back original value
        expect!(data != original);
        Ok(())
    }

    fn test_random_rng(&mut self) -> TestResult {
        let mut rng = oak::rand::OakRng {};
        let x1 = rng.gen::<u64>();
        let x2 = rng.gen::<u64>();
        expect!(x1 != x2);
        Ok(())
    }

    fn test_channel_handle_reuse(&mut self) -> TestResult {
        // Set up a fresh channel with a pending message so wait_on_channels
        // doesn't block.
        let (out_handle, in_handle) =
            oak::channel_create("Test", &Label::public_untrusted()).unwrap();
        let data = vec![0x01, 0x02, 0x03];
        expect_eq!(Ok(()), oak::channel_write(out_handle, &data, &[]));

        // Read from an invalid handle.
        let mut buffer = Vec::<u8>::with_capacity(5);
        let mut handles = Vec::with_capacity(5);
        expect_eq!(
            Err(OakStatus::ErrBadHandle),
            oak::channel_read(
                oak::ReadHandle { handle: 9_987_123 },
                &mut buffer,
                &mut handles
            )
        );
        // Wait on an invalid handle.
        expect_eq!(
            Ok(vec![
                ChannelReadStatus::ReadReady,
                ChannelReadStatus::InvalidChannel
            ]),
            oak::wait_on_channels(&[in_handle, oak::ReadHandle { handle: 9_987_321 }])
        );

        // Close both of the previously mentioned invalid handles.
        expect_eq!(Err(OakStatus::ErrBadHandle), oak::channel_close(9_987_123));
        expect_eq!(Err(OakStatus::ErrBadHandle), oak::channel_close(9_987_321));

        expect_eq!(Ok(()), oak::channel_close(out_handle.handle));
        expect_eq!(Ok(()), oak::channel_close(in_handle.handle));
        Ok(())
    }

    fn test_log(&mut self) -> TestResult {
        // Try out all the levels.
        trace!("This is a trace level log");
        debug!("This is a debug level log");
        info!("This is a info level log");
        warn!("This is a warn level log");
        error!("This is an error level log");
        Ok(())
    }

    fn test_direct_log(&mut self) -> TestResult {
        // Send a message directly to a fresh logging Node (not via the log facade).
        // Include some handles which will be ignored.
        let (logging_handle, read_handle) = oak::channel_create("Test", &Label::public_untrusted())
            .expect("could not create channel");
        oak::node_create(
            "log",
            &oak::node_config::log(),
            &Label::public_untrusted(),
            read_handle,
        )
        .expect("could not create node");
        oak::channel_close(read_handle.handle).expect("could not close channel");

        expect!(is_valid(logging_handle.handle));
        let (out_handle, in_handle) = oak::channel_create("Test", &Label::public_untrusted())
            .expect("could not create channel");

        oak::channel_write(
            logging_handle,
            "Malformed message sent direct to logging channel!".as_bytes(),
            &[in_handle.handle, out_handle.handle],
        )
        .expect("could not write to channel");

        let mut bytes = Vec::new();
        oak_services::proto::oak::log::LogMessage {
            level: oak_services::proto::oak::log::Level::Info as i32,
            file: "abitest".to_string(),
            line: 1988,
            message: "Wellformed message sent direct to logging channel!".to_string(),
        }
        .encode(&mut bytes)
        .unwrap();

        oak::channel_write(
            logging_handle,
            bytes.as_ref(),
            &[in_handle.handle, out_handle.handle],
        )
        .expect("could not write to channel");

        expect_eq!(Ok(()), oak::channel_close(out_handle.handle));
        expect_eq!(Ok(()), oak::channel_close(in_handle.handle));
        expect_eq!(Ok(()), oak::channel_close(logging_handle.handle));
        Ok(())
    }

    fn test_backend_roundtrip(&mut self) -> TestResult {
        // Make a collection of new channels for the backend nodes to read from,
        // and send the read handles to each backend node.
        const CHANNEL_COUNT: usize = 3;
        let mut read_handles = Vec::with_capacity(CHANNEL_COUNT);
        let mut write_handles = Vec::with_capacity(CHANNEL_COUNT);
        for _ in 0..CHANNEL_COUNT {
            let (new_write, new_read) =
                oak::channel_create("Test", &Label::public_untrusted()).unwrap();
            write_handles.push(new_write);
            read_handles.push(new_read.handle);
        }
        for j in 0..BACKEND_COUNT {
            expect_eq!(
                Ok(()),
                oak::channel_write(self.backend_out[j], &[], &read_handles)
            );
        }
        for new_read in read_handles.iter() {
            oak::channel_close(*new_read).expect("could not close channel");
        }

        // Ask the backend node to transmute something by writing a serialized
        // request to one of the new channels that the backends just received
        // the read handles for.
        for new_write in write_handles.iter() {
            let internal_req = InternalMessage {
                msg: "aaa".to_string(),
            };
            info!(
                "sending message to new channel {:?}: {:?}",
                new_write.handle, internal_req,
            );
            let new_channel = oak::io::Sender::new(*new_write);
            new_channel
                .send(&internal_req)
                .expect("could not send request over channel");
            oak::channel_close(new_write.handle).expect("could not close channel");

            // Block until there is a response from one of the backends
            // available.
            let readies = oak::wait_on_channels(&self.backend_in).map_err(OakError::OakStatus)?;

            // Expect exactly one of the backends to have received
            // the message.
            let mut buffer = Vec::<u8>::with_capacity(256);
            let mut new_in_channel = oak::ReadHandle { handle: 0 };
            for (j, ready) in readies.iter().enumerate() {
                if *ready == ChannelReadStatus::ReadReady {
                    info!("got response from backend[{}]", j);
                    expect_eq!(0, new_in_channel.handle);
                    let mut handles = Vec::with_capacity(1);
                    expect_eq!(
                        Ok(()),
                        oak::channel_read(self.backend_in[j], &mut buffer, &mut handles)
                    );
                    new_in_channel.handle = handles[0];
                }
            }

            // Expect the response to hold a channel read handle.
            // Read the actual transmuted message from this new channel.
            expect_eq!(
                Ok(()),
                oak::channel_read(new_in_channel, &mut buffer, &mut vec![])
            );
            let serialized_rsp = String::from_utf8(buffer).unwrap();
            let internal_rsp: InternalMessage = serde_json::from_str(&serialized_rsp)?;
            expect_eq!("aaaxxx", internal_rsp.msg);

            // Drop the new read channel now we have got the response.
            expect_eq!(Ok(()), oak::channel_close(new_in_channel.handle));
        }

        // Send a single byte to each backend Node, so they get woken up to detect
        // orphaned channels.
        for j in 0..BACKEND_COUNT {
            expect_eq!(
                Ok(()),
                oak::channel_write(self.backend_out[j], &[0x00], &[])
            );
        }
        Ok(())
    }
    fn test_storage(&mut self) -> TestResult {
        let storage = self.storage.as_mut().ok_or_else(|| {
            Box::new(std::io::Error::new(
                std::io::ErrorKind::Other,
                "no storage channel available",
            ))
        })?;
        let key = b"test-key-0";
        let value = b"test-value-0";
        storage
            .write(&self.storage_name, key, value)
            .map_err(from_proto)?;

        let got = storage.read(&self.storage_name, key).map_err(from_proto)?;
        expect_eq!(value.to_vec(), got);

        let key2 = b"test-key-bogus";
        let got = storage.read(&self.storage_name, key2);
        expect_matches!(got, Err(_));
        expect_eq!(grpc::Code::NotFound as i32, got.unwrap_err().code);

        let got = storage.read(&self.storage_name, key).map_err(from_proto)?;
        expect_eq!(value.to_vec(), got);

        storage
            .delete(&self.storage_name, key)
            .map_err(from_proto)?;

        let got = storage.read(&self.storage_name, key);
        expect_matches!(got, Err(_));
        expect_eq!(grpc::Code::NotFound as i32, got.unwrap_err().code);

        storage
            .delete(&self.storage_name, key)
            .map_err(from_proto)?;
        storage
            .delete(&self.storage_name, key2)
            .map_err(from_proto)?;

        Ok(())
    }
    fn test_absent_storage(&mut self) -> TestResult {
        // Expect to have a channel to a storage pseudo-Node, but the remote
        // storage provider is unavailable.
        let storage = self.absent_storage.as_mut().ok_or_else(|| {
            Box::new(std::io::Error::new(
                std::io::ErrorKind::Other,
                "no storage channel available",
            ))
        })?;
        let key = b"a-test-key-0";
        let value = b"a-test-value-0";

        let got = storage.write(&self.storage_name, key, value);
        expect_matches!(got, Err(_));
        expect_eq!(grpc::Code::Unavailable as i32, got.unwrap_err().code);
        let got = storage.read(&self.storage_name, key);
        expect_matches!(got, Err(_));
        expect_eq!(grpc::Code::Unavailable as i32, got.unwrap_err().code);
        let got = storage.delete(&self.storage_name, key);
        expect_matches!(got, Err(_));
        expect_eq!(grpc::Code::Unavailable as i32, got.unwrap_err().code);

        Ok(())
    }

    fn test_grpc_server_second(&mut self) -> TestResult {
        // Create a second gRPC server Node on a different port.
        let result = oak::grpc::server::init(ADDITIONAL_TEST_GRPC_SERVER_ADDR);
        expect_matches!(result, Ok(_));
        let invocation_receiver = result.unwrap();
        // Close the only read-handle for the invocation handle, which should
        // trigger the gRPC server pseudo-Node to terminate (but we can't
        // check that here).
        expect_eq!(Ok(()), invocation_receiver.close());
        Ok(())
    }

    fn test_grpc_server_invalid_address(&mut self) -> TestResult {
        // Attempt to create an additional gRPC server with an invalid local address.
        expect_eq!(
            Some(OakStatus::ErrInvalidArgs),
            oak::grpc::server::init("10 Downing Street").err()
        );
        Ok(())
    }

    // Under the covers, the oak::grpc::server::init() helper performs
    // several steps. Test various failure conditions for each of those steps.
    // We can't really check any failures, but hopefully nothing crashes...
    fn test_grpc_server_fail_no_handle(&mut self) -> TestResult {
        let config = oak::node_config::grpc_server(ADDITIONAL_TEST_FAIL_SERVER_ADDR);
        // Rather than passing the newly-created Node a message with a write handle
        // for an invocation channel in it, instead pass it a message with data.
        let (wh, rh) = oak::channel_create("Test", &Label::public_untrusted())
            .expect("could not create channel");
        expect_eq!(
            Ok(()),
            oak::node_create("grpc_server", &config, &Label::public_untrusted(), rh)
        );
        oak::channel_write(wh, &[0x01, 0x02], &[]).expect("could not write to channel");
        expect_eq!(Ok(()), oak::channel_close(rh.handle));
        expect_eq!(Ok(()), oak::channel_close(wh.handle));
        Ok(())
    }
    fn test_grpc_server_fail_read_handle(&mut self) -> TestResult {
        let config = oak::node_config::grpc_server(ADDITIONAL_TEST_FAIL_SERVER_ADDR);

        // Rather than passing the newly-created Node a message with a write handle
        // for an invocation channel in it, instead pass it a message with a single
        // read handle.
        let (wh, rh) = oak::channel_create("Test", &Label::public_untrusted())
            .expect("could not create channel");
        expect_eq!(
            Ok(()),
            oak::node_create("grpc_server", &config, &Label::public_untrusted(), rh)
        );
        oak::channel_write(wh, &[], &[rh.handle]).expect("could not write to channel");
        expect_eq!(Ok(()), oak::channel_close(rh.handle));
        expect_eq!(Ok(()), oak::channel_close(wh.handle));
        Ok(())
    }
    fn test_grpc_server_fail_two_handles(&mut self) -> TestResult {
        let config = oak::node_config::grpc_server(ADDITIONAL_TEST_FAIL_SERVER_ADDR);

        // Rather than passing the newly-created Node a message with a write handle
        // for an invocation channel in it, instead pass it a message with a write
        // handle and a read handle.
        let (wh, rh) = oak::channel_create("Test", &Label::public_untrusted())
            .expect("could not create channel");
        expect_eq!(
            Ok(()),
            oak::node_create("grpc_server", &config, &Label::public_untrusted(), rh)
        );
        oak::channel_write(wh, &[], &[wh.handle, rh.handle]).expect("could not write to channel");
        expect_eq!(Ok(()), oak::channel_close(rh.handle));
        expect_eq!(Ok(()), oak::channel_close(wh.handle));
        Ok(())
    }
    fn test_grpc_client_unary_method(&mut self) -> TestResult {
        let grpc_stub = oak::grpc::client::init(GRPC_CLIENT_ADDRESS)
            .map(OakAbiTestServiceClient)
            .map_err(|_err| {
                Box::new(std::io::Error::new(
                    std::io::ErrorKind::Other,
                    "no gRPC client channel available",
                ))
            })?;

        // Successful unary method invocation of external service via gRPC client pseudo-Node.
        let ok_req = GrpcTestRequest {
            method_result: Some(proto::grpc_test_request::MethodResult::OkText(
                "test".to_string(),
            )),
        };
        let ok_rsp = GrpcTestResponse {
            text: "test".to_string(),
        };
        expect_eq!(grpc_stub.unary_method(ok_req), Ok(ok_rsp));

        // Errored unary method invocation of external service via gRPC client pseudo-Node.
        let err_req = GrpcTestRequest {
            method_result: Some(proto::grpc_test_request::MethodResult::ErrCode(
                grpc::Code::FailedPrecondition as i32,
            )),
        };
        let result = grpc_stub.unary_method(err_req);
        expect_matches!(result, Err(_));
        expect_eq!(
            grpc::Code::FailedPrecondition as i32,
            result.unwrap_err().code
        );

        Ok(())
    }
    fn test_grpc_client_server_streaming_method(&mut self) -> TestResult {
        let grpc_stub = oak::grpc::client::init(GRPC_CLIENT_ADDRESS)
            .map(OakAbiTestServiceClient)
            .map_err(|_err| {
                Box::new(std::io::Error::new(
                    std::io::ErrorKind::Other,
                    "no gRPC client channel available",
                ))
            })?;
        // Successful server-streaming method invocation of external service via
        // gRPC client pseudo-Node.
        let ok_req = GrpcTestRequest {
            method_result: Some(proto::grpc_test_request::MethodResult::OkText(
                "test".to_string(),
            )),
        };
        let ok_rsp = GrpcTestResponse {
            text: "test".to_string(),
        };
        let receiver = grpc_stub
            .server_streaming_method(ok_req)
            .map_err(from_proto)?;
        let mut count = 0;
        loop {
            match receiver.receive() {
                Ok(grpc_rsp) => {
                    // TODO(#592): get typed response directly from receiver.
                    expect_eq!(
                        oak::grpc::Code::Ok as i32,
                        grpc_rsp.status.unwrap_or_default().code
                    );
                    let rsp = GrpcTestResponse::decode(grpc_rsp.rsp_msg.as_slice())
                        .expect("failed to parse GrpcTestResponse");
                    expect_eq!(rsp.clone(), ok_rsp.clone());
                    count += 1;
                }
                Err(OakError::OakStatus(OakStatus::ErrBadHandle)) => break,
                Err(OakError::OakStatus(OakStatus::ErrChannelClosed)) => break,
                Err(e) => return Err(Box::new(e)),
            }
        }
        expect_eq!(2, count);
        receiver.close().expect("failed to close receiver");

        // Errored server-streaming method invocation of external service via
        // gRPC client pseudo-Node.
        let err_req = GrpcTestRequest {
            method_result: Some(proto::grpc_test_request::MethodResult::ErrCode(
                grpc::Code::FailedPrecondition as i32,
            )),
        };
        let receiver = grpc_stub
            .server_streaming_method(err_req)
            .map_err(from_proto)?;
        let mut seen_err_code = false;
        loop {
            match receiver.receive() {
                Ok(grpc_rsp) => {
                    expect_eq!(
                        grpc::Code::FailedPrecondition as i32,
                        grpc_rsp.status.unwrap_or_default().code
                    );
                    seen_err_code = true;
                }
                Err(OakError::OakStatus(OakStatus::ErrBadHandle)) => break,
                Err(OakError::OakStatus(OakStatus::ErrChannelClosed)) => break,
                Err(e) => return Err(Box::new(e)),
            }
        }
        expect!(seen_err_code);
        receiver.close().expect("failed to close receiver");
        Ok(())
    }

    fn test_absent_grpc_client_unary_method(&mut self) -> TestResult {
        // Expect to have a channel to a gRPC client pseudo-Node, but the remote
        // gRPC service is unavailable.
        let grpc_stub = oak::grpc::client::init("https://test.invalid:9999")
            .map(OakAbiTestServiceClient)
            .map_err(|_err| {
                Box::new(std::io::Error::new(
                    std::io::ErrorKind::Other,
                    "no gRPC client channel available",
                ))
            })?;
        let req = GrpcTestRequest {
            method_result: Some(proto::grpc_test_request::MethodResult::OkText(
                "test".to_string(),
            )),
        };

        // Attempting to invoke a unary method should fail.
        let result = grpc_stub.unary_method(req);
        info!("absent.unary_method() -> {:?}", result);
        expect_matches!(result, Err(_));
        Ok(())
    }

    fn test_absent_grpc_client_server_streaming_method(&mut self) -> TestResult {
        // Expect to have a channel to a gRPC client pseudo-Node, but the remote
        // gRPC service is unavailable.
        let grpc_stub = oak::grpc::client::init("https://test.invalid:9999")
            .map(OakAbiTestServiceClient)
            .map_err(|_err| {
                Box::new(std::io::Error::new(
                    std::io::ErrorKind::Other,
                    "no gRPC client channel available",
                ))
            })?;
        let req = GrpcTestRequest {
            method_result: Some(proto::grpc_test_request::MethodResult::OkText(
                "test".to_string(),
            )),
        };

        // Attempting to invoke a server-streaming method should fail.
        info!("absent.server_streaming_method()");
        let receiver = grpc_stub.server_streaming_method(req).map_err(from_proto)?;
        loop {
            let result = receiver.receive();
            info!("absent.server_streaming_method().receive() -> {:?}", result);
            match result {
                Ok(grpc_rsp) => {
                    expect!(grpc_rsp.status.unwrap_or_default().code != grpc::Code::Ok as i32);
                }
                Err(OakError::OakStatus(OakStatus::ErrBadHandle)) => break,
                Err(OakError::OakStatus(OakStatus::ErrChannelClosed)) => break,
                Err(e) => return Err(Box::new(e)),
            }
        }
        receiver.close().expect("failed to close receiver");

        Ok(())
    }

    fn test_http_server_create(&mut self) -> TestResult {
        // Create an HTTP server pseudo-Node.
        let result = oak::http::server::init(ADDITIONAL_TEST_HTTP_SERVER_ADDR);
        expect_matches!(result, Ok(_));
        let invocation_receiver = result.unwrap();
        // Close the only read-handle for the invocation handle, which should
        // trigger the HTTP server pseudo-Node to terminate (but we can't
        // check that here).
        expect_eq!(Ok(()), invocation_receiver.close());
        Ok(())
    }

    fn test_http_server_reserved_port(&mut self) -> TestResult {
        // Attempt to create an HTTP server with an invalid local port.
        expect_eq!(
            Some(OakStatus::ErrInvalidArgs),
            oak::http::server::init("[::]:1001").err()
        );
        Ok(())
    }

    fn test_http_server_invalid_address(&mut self) -> TestResult {
        // Attempt to create an HTTP server with an invalid local address.
        expect_eq!(
            Some(OakStatus::ErrInvalidArgs),
            oak::http::server::init("Platform 9 3/4").err()
        );
        Ok(())
    }

    // Under the covers, the oak::http::server::init() helper performs several steps. Test various
    // failure conditions for each of those steps. We can't really check any failures, but
    // hopefully nothing crashes...
    fn test_http_server_fail_no_handle(&mut self) -> TestResult {
        let config = oak::node_config::http_server(ADDITIONAL_TEST_FAIL_SERVER_ADDR);

        // Rather than passing the newly-created Node a message with a write handle
        // for an invocation channel in it, instead pass it a message with data.
        let (wh, rh) = oak::channel_create("Test", &Label::public_untrusted())
            .expect("could not create channel");
        expect_eq!(
            Ok(()),
            oak::node_create("http_server", &config, &Label::public_untrusted(), rh)
        );
        oak::channel_write(wh, &[0x01, 0x02], &[]).expect("could not write to channel");
        expect_eq!(Ok(()), oak::channel_close(rh.handle));
        expect_eq!(Ok(()), oak::channel_close(wh.handle));
        Ok(())
    }
    fn test_http_server_fail_read_handle(&mut self) -> TestResult {
        let config = oak::node_config::http_server(ADDITIONAL_TEST_FAIL_SERVER_ADDR);

        // Rather than passing the newly-created Node a message with a write handle
        // for an invocation channel in it, instead pass it a message with a single
        // read handle.
        let (wh, rh) = oak::channel_create("Test", &Label::public_untrusted())
            .expect("could not create channel");
        expect_eq!(
            Ok(()),
            oak::node_create("http_server", &config, &Label::public_untrusted(), rh)
        );
        oak::channel_write(wh, &[], &[rh.handle]).expect("could not write to channel");
        expect_eq!(Ok(()), oak::channel_close(rh.handle));
        expect_eq!(Ok(()), oak::channel_close(wh.handle));
        Ok(())
    }
    fn test_http_server_fail_two_handles(&mut self) -> TestResult {
        let config = oak::node_config::http_server(ADDITIONAL_TEST_FAIL_SERVER_ADDR);

        // Rather than passing the newly-created Node a message with a write handle
        // for an invocation channel in it, instead pass it a message with a write
        // handle and a read handle.
        let (wh, rh) = oak::channel_create("Test", &Label::public_untrusted())
            .expect("could not create channel");
        expect_eq!(
            Ok(()),
            oak::node_create("http_server", &config, &Label::public_untrusted(), rh)
        );
        oak::channel_write(wh, &[], &[wh.handle, rh.handle]).expect("could not write to channel");
        expect_eq!(Ok(()), oak::channel_close(rh.handle));
        expect_eq!(Ok(()), oak::channel_close(wh.handle));
        Ok(())
    }

    fn test_roughtime_client(&mut self) -> TestResult {
        let roughtime = self.roughtime.as_mut().ok_or_else(|| {
            Box::new(std::io::Error::new(
                std::io::ErrorKind::Other,
                "no Roughtime channel available",
            ))
        })?;

        let mut times: [std::time::Duration; 2] = [std::time::Duration::from_millis(0); 2];
        for (i, time) in times.iter_mut().enumerate() {
            let result = roughtime.get_roughtime();
            expect_matches!(result, Ok(_));
            *time = result.unwrap();

            // Use chrono library to convert to wall clock datetime.
            let dt = chrono::DateTime::<chrono::Utc>::from_utc(
                chrono::NaiveDateTime::from_timestamp(
                    time.as_secs().try_into().unwrap(),
                    time.subsec_nanos(),
                ),
                chrono::Utc,
            );
            info!("Roughtime[{}] is {}", i, dt);
        }

        expect!(times[0] <= times[1]);
        Ok(())
    }
    fn test_roughtime_client_misconfig(&mut self) -> TestResult {
        let roughtime = self.misconfigured_roughtime.as_mut().ok_or_else(|| {
            Box::new(std::io::Error::new(
                std::io::ErrorKind::Other,
                "no Roughtime channel available",
            ))
        })?;

        // This Roughtime pseudo-Node has been configured to require more
        // overlapping intervals than there are servers available, so will
        // always fail to get the time.
        let result = roughtime.get_roughtime();
        expect_matches!(result, Err(_));
        Ok(())
    }

    fn test_crypto_bind(&mut self) -> TestResult {
        let crypto = self.crypto.as_ref().ok_or_else(|| {
            Box::new(std::io::Error::new(
                std::io::ErrorKind::Other,
                "no crypto channel available",
            ))
        })?;
        let aead_kh = crypto.generate_named("AES256_GCM").map_err(from_proto)?;
        let daead_kh = crypto.generate_named("AES256_SIV").map_err(from_proto)?;
        let ct = crypto
            .encrypt_deterministically(daead_kh, b"the plaintext", b"aad")
            .map_err(from_proto)?;

        // Bind the DAEAD keyset with the outer AEAD keyset, then recover it again.
        let encrypted_keyset = crypto
            .bind(aead_kh, daead_kh, oak::crypto::KeysetFormat::Json)
            .map_err(from_proto)?;
        info!(
            "Encrypted keyset: {}",
            String::from_utf8_lossy(&encrypted_keyset)
        );
        let recovered_kh = crypto
            .unbind(aead_kh, &encrypted_keyset, oak::crypto::KeysetFormat::Json)
            .map_err(from_proto)?;

        // Can decrypt with recovered DAEAD keyset.
        let pt = crypto
            .decrypt_deterministically(recovered_kh, &ct, b"aad")
            .map_err(from_proto)?;
        expect_eq!(b"the plaintext".to_vec(), pt);
        Ok(())
    }

    fn test_crypto_bind_fail(&mut self) -> TestResult {
        let crypto = self.crypto.as_ref().ok_or_else(|| {
            Box::new(std::io::Error::new(
                std::io::ErrorKind::Other,
                "no crypto channel available",
            ))
        })?;
        let aead_kh = crypto.generate_named("AES256_GCM").map_err(from_proto)?;
        let daead_kh = crypto.generate_named("AES256_SIV").map_err(from_proto)?;
        let encrypted_keyset = crypto
            .bind(aead_kh, daead_kh, oak::crypto::KeysetFormat::Json)
            .map_err(from_proto)?;

        let result = crypto.bind(aead_kh, 9999, oak::crypto::KeysetFormat::Json);
        expect_matches!(result, Err(_));
        let result = crypto.bind(9999, daead_kh, oak::crypto::KeysetFormat::Json);
        expect_matches!(result, Err(_));

        let result = crypto.unbind(9999, &encrypted_keyset, oak::crypto::KeysetFormat::Json);
        expect_matches!(result, Err(_));
        let result = crypto.unbind(aead_kh, &[1, 2, 3], oak::crypto::KeysetFormat::Json);
        expect_matches!(result, Err(_));

        Ok(())
    }

    fn test_crypto_daead(&mut self) -> TestResult {
        let crypto = self.crypto.as_ref().ok_or_else(|| {
            Box::new(std::io::Error::new(
                std::io::ErrorKind::Other,
                "no crypto channel available",
            ))
        })?;
        let kh = crypto
            .generate(tink_proto::KeyTemplate {
                type_url: "type.googleapis.com/google.crypto.tink.AesSivKey".to_string(),
                value: vec![],
                output_prefix_type: tink_proto::OutputPrefixType::Tink as i32,
            })
            .map_err(from_proto)?;

        let ct = crypto
            .encrypt_deterministically(kh, b"the plaintext", b"aad")
            .map_err(from_proto)?;
        let pt = crypto
            .decrypt_deterministically(kh, &ct, b"aad")
            .map_err(from_proto)?;
        expect_eq!(b"the plaintext".to_vec(), pt);
        Ok(())
    }

    fn test_crypto_daead_fail(&mut self) -> TestResult {
        let crypto = self.crypto.as_ref().ok_or_else(|| {
            Box::new(std::io::Error::new(
                std::io::ErrorKind::Other,
                "no crypto channel available",
            ))
        })?;

        // Invalid keyset handle.
        let kh = 999;
        let result = crypto.encrypt_deterministically(kh, b"the plaintext", b"aad");
        expect_matches!(result, Err(_));
        let result = crypto.decrypt_deterministically(kh, b"alleged ciphertext", b"aad");
        expect_matches!(result, Err(_));

        // Keyset handle for the wrong type of key material.
        let kh = crypto
            .generate_named("CHACHA20_POLY1305")
            .map_err(from_proto)?;
        let result = crypto.encrypt_deterministically(kh, b"the plaintext", b"aad");
        expect_matches!(result, Err(_));
        let result = crypto.decrypt_deterministically(kh, b"alleged ciphertext", b"aad");
        expect_matches!(result, Err(_));

        Ok(())
    }

    fn test_crypto_aead(&mut self) -> TestResult {
        let crypto = self.crypto.as_ref().ok_or_else(|| {
            Box::new(std::io::Error::new(
                std::io::ErrorKind::Other,
                "no crypto channel available",
            ))
        })?;
        let kh = crypto
            .generate_named("CHACHA20_POLY1305")
            .map_err(from_proto)?;

        let ct = crypto
            .encrypt(kh, b"the plaintext", b"aad")
            .map_err(from_proto)?;
        let pt = crypto.decrypt(kh, &ct, b"aad").map_err(from_proto)?;
        expect_eq!(b"the plaintext".to_vec(), pt);
        Ok(())
    }

    fn test_crypto_aead_fail(&mut self) -> TestResult {
        let crypto = self.crypto.as_ref().ok_or_else(|| {
            Box::new(std::io::Error::new(
                std::io::ErrorKind::Other,
                "no crypto channel available",
            ))
        })?;

        // Invalid keyset handle.
        let kh = 999;
        let result = crypto.encrypt(kh, b"the plaintext", b"aad");
        expect_matches!(result, Err(_));
        let result = crypto.decrypt(kh, b"alleged ciphertext", b"aad");
        expect_matches!(result, Err(_));

        // Keyset handle for the wrong type of key material.
        let kh = crypto.generate_named("AES256_SIV").map_err(from_proto)?;
        let result = crypto.encrypt(kh, b"the plaintext", b"aad");
        expect_matches!(result, Err(_));
        let result = crypto.decrypt(kh, b"alleged ciphertext", b"aad");
        expect_matches!(result, Err(_));

        Ok(())
    }

    fn test_crypto_mac(&mut self) -> TestResult {
        let crypto = self.crypto.as_ref().ok_or_else(|| {
            Box::new(std::io::Error::new(
                std::io::ErrorKind::Other,
                "no crypto channel available",
            ))
        })?;
        let kh = crypto
            .generate_named("HMAC_SHA256_256BITTAG")
            .map_err(from_proto)?;

        let mac = crypto.compute_mac(kh, b"the data").map_err(from_proto)?;
        crypto
            .verify_mac(kh, b"the data", &mac)
            .map_err(from_proto)?;
        Ok(())
    }

    fn test_crypto_mac_fail(&mut self) -> TestResult {
        let crypto = self.crypto.as_ref().ok_or_else(|| {
            Box::new(std::io::Error::new(
                std::io::ErrorKind::Other,
                "no crypto channel available",
            ))
        })?;

        // Invalid keyset handle.
        let kh = 999;
        let result = crypto.compute_mac(kh, b"the data");
        expect_matches!(result, Err(_));
        let result = crypto.verify_mac(kh, b"fake mac", b"the data");
        expect_matches!(result, Err(_));

        // Keyset handle for the wrong type of key material.
        let kh = crypto.generate_named("AES256_SIV").map_err(from_proto)?;
        let result = crypto.compute_mac(kh, b"the data");
        expect_matches!(result, Err(_));
        let result = crypto.verify_mac(kh, b"fake mac", b"the data");
        expect_matches!(result, Err(_));

        Ok(())
    }

    fn test_crypto_prf(&mut self) -> TestResult {
        let crypto = self.crypto.as_ref().ok_or_else(|| {
            Box::new(std::io::Error::new(
                std::io::ErrorKind::Other,
                "no crypto channel available",
            ))
        })?;
        let kh = crypto
            .generate_named("HMAC_SHA256_PRF")
            .map_err(from_proto)?;

        let _prf = crypto
            .compute_prf(kh, b"the data", 10)
            .map_err(from_proto)?;
        Ok(())
    }

    fn test_crypto_prf_fail(&mut self) -> TestResult {
        let crypto = self.crypto.as_ref().ok_or_else(|| {
            Box::new(std::io::Error::new(
                std::io::ErrorKind::Other,
                "no crypto channel available",
            ))
        })?;

        // Invalid keyset handle.
        let kh = 999;
        let result = crypto.compute_prf(kh, b"the data", 10);
        expect_matches!(result, Err(_));

        // Keyset handle for the wrong type of key material.
        let kh = crypto.generate_named("AES256_SIV").map_err(from_proto)?;
        let result = crypto.compute_prf(kh, b"the data", 10);
        expect_matches!(result, Err(_));

        Ok(())
    }

    fn test_crypto_sign(&mut self) -> TestResult {
        let crypto = self.crypto.as_ref().ok_or_else(|| {
            Box::new(std::io::Error::new(
                std::io::ErrorKind::Other,
                "no crypto channel available",
            ))
        })?;
        let kh = crypto.generate_named("ECDSA_P256").map_err(from_proto)?;

        let sig = crypto.sign(kh, b"the data").map_err(from_proto)?;

        let pub_kh = crypto.public(kh).map_err(from_proto)?;
        crypto
            .verify(pub_kh, b"the data", &sig)
            .map_err(from_proto)?;
        Ok(())
    }

    fn test_crypto_sign_fail(&mut self) -> TestResult {
        let crypto = self.crypto.as_ref().ok_or_else(|| {
            Box::new(std::io::Error::new(
                std::io::ErrorKind::Other,
                "no crypto channel available",
            ))
        })?;

        // Invalid keyset handle.
        let kh = 999;
        let result = crypto.sign(kh, b"the data");
        expect_matches!(result, Err(_));
        let result = crypto.verify(kh, b"the data", b"fake sig");
        expect_matches!(result, Err(_));

        // Keyset handle for the wrong type of key material.
        let kh = crypto.generate_named("AES256_SIV").map_err(from_proto)?;
        let result = crypto.sign(kh, b"the data");
        expect_matches!(result, Err(_));
        let result = crypto.verify(kh, b"the data", b"fake sig");
        expect_matches!(result, Err(_));

        Ok(())
    }

    fn test_grpc_server_pseudo_node_privilege(&mut self) -> TestResult {
        // gRPC server pseudo node can be created even with Top confidentiality.
        // TODO(#1631): Update test if the gRPC server pseudo node's declassification privilege is
        // lowered to be the top of the user sub-lattice, rather than the global top.
        let top_label = oak_abi::label::confidentiality_label(oak_abi::label::top());
        let config = oak::node_config::grpc_server(ADDITIONAL_TEST_GRPC_SERVER_ADDR_2);
        let (wh, rh) = oak::channel_create("Test", &top_label).expect("could not create channel");
        expect_eq!(
            Ok(()),
            oak::node_create("grpc_server", &config, &top_label, rh)
        );
        expect_eq!(Ok(()), oak::channel_close(rh.handle));
        expect_eq!(Ok(()), oak::channel_close(wh.handle));
        Ok(())
    }

    fn test_http_server_pseudo_node_privilege(&mut self) -> TestResult {
        // HTTP server pseudo node can be created even with Top confidentiality.
        // TODO(#1631): Update test if the HTTP server pseudo node's declassification privilege is
        // lowered to be the top of the user sub-lattice, rather than the global top.
        let top_label = oak_abi::label::confidentiality_label(oak_abi::label::top());
        let config = oak::node_config::http_server(ADDITIONAL_TEST_HTTP_SERVER_ADDR_2);
        let (wh, rh) = oak::channel_create("Test", &top_label).expect("could not create channel");
        expect_eq!(
            Ok(()),
            oak::node_create("http_server", &config, &top_label, rh)
        );
        expect_eq!(Ok(()), oak::channel_close(rh.handle));
        expect_eq!(Ok(()), oak::channel_close(wh.handle));
        Ok(())
    }

    fn test_grpc_client_pseudo_node_privilege(&mut self) -> TestResult {
        // gRPC client pseudo node can be created with TLS endpoint confidentiality tag matching its
        {
            // URI authority.
            let label = oak_abi::label::confidentiality_label(oak_abi::label::tls_endpoint_tag(
                GRPC_CLIENT_ADDRESS
                    .parse::<Uri>()
                    .unwrap()
                    .authority()
                    .unwrap()
                    .as_str(),
            ));
            let config = oak::node_config::grpc_client(GRPC_CLIENT_ADDRESS);
            let (wh, rh) = oak::channel_create("Test", &label).expect("could not create channel");
            expect_eq!(Ok(()), oak::node_create("grpc_client", &config, &label, rh));
            expect_eq!(Ok(()), oak::channel_close(rh.handle));
            expect_eq!(Ok(()), oak::channel_close(wh.handle));
        }

        // gRPC client pseudo node can not be created with non-matching TLS endpoint
        // confidentiality tag.
        {
            let label = oak_abi::label::confidentiality_label(oak_abi::label::tls_endpoint_tag(
                "google.com",
            ));
            let config = oak::node_config::grpc_client(GRPC_CLIENT_ADDRESS);
            let (wh, rh) = oak::channel_create("Test", &label).expect("could not create channel");
            expect_eq!(
                Err(OakStatus::ErrPermissionDenied),
                oak::node_create("grpc_client", &config, &label, rh)
            );
            expect_eq!(Ok(()), oak::channel_close(rh.handle));
            expect_eq!(Ok(()), oak::channel_close(wh.handle));
        }
        Ok(())
    }

    fn test_http_client_pseudo_node_privilege(&mut self) -> TestResult {
        // Public HTTP client pseudo node can be created with empty authority, and a public label.
        {
            let label = Label::public_untrusted();
            let config = oak::node_config::http_client("");
            let (wh, rh) = oak::channel_create("Test", &label).expect("could not create channel");
            expect_eq!(Ok(()), oak::node_create("http_client", &config, &label, rh));
            expect_eq!(Ok(()), oak::channel_close(rh.handle));
            expect_eq!(Ok(()), oak::channel_close(wh.handle));
        }

        let uri = HTTP_CLIENT_ADDRESS.parse::<Uri>().unwrap();
        let authority = uri.authority().unwrap().as_str();

        // HTTP client pseudo node can be created with TLS endpoint confidentiality tag matching its
        // URI authority.
        {
            let label =
                oak_abi::label::confidentiality_label(oak_abi::label::tls_endpoint_tag(authority));
            let config = oak::node_config::http_client(authority);
            let (wh, rh) = oak::channel_create("Test", &label).expect("could not create channel");
            expect_eq!(Ok(()), oak::node_create("http_client", &config, &label, rh));
            expect_eq!(Ok(()), oak::channel_close(rh.handle));
            expect_eq!(Ok(()), oak::channel_close(wh.handle));
        }

        // HTTP client pseudo node can not be created with non-matching TLS endpoint
        // confidentiality tag.
        {
            let label = oak_abi::label::confidentiality_label(oak_abi::label::tls_endpoint_tag(
                "google.com",
            ));
            let config = oak::node_config::http_client(authority);
            let (wh, rh) = oak::channel_create("Test", &label).expect("could not create channel");
            expect_eq!(
                Err(OakStatus::ErrPermissionDenied),
                oak::node_create("http_client", &config, &label, rh)
            );
            expect_eq!(Ok(()), oak::channel_close(rh.handle));
            expect_eq!(Ok(()), oak::channel_close(wh.handle));
        }
        Ok(())
    }

    fn test_roughtime_client_pseudo_node_privilege(&mut self) -> TestResult {
        // Roughtime client pseudo node cannot be created with a non-public label.
        let label = oak_abi::label::confidentiality_label(oak_abi::label::tls_endpoint_tag(
            GRPC_CLIENT_ADDRESS
                .parse::<Uri>()
                .unwrap()
                .authority()
                .unwrap()
                .as_str(),
        ));
        let config = NodeConfiguration {
            config_type: Some(ConfigType::RoughtimeClientConfig(
                RoughtimeClientConfiguration {
                    ..Default::default()
                },
            )),
        };
        let (wh, rh) = oak::channel_create("Test", &label).expect("could not create channel");
        expect_eq!(
            Err(OakStatus::ErrPermissionDenied),
            oak::node_create("roughtime_client", &config, &label, rh)
        );
        expect_eq!(Ok(()), oak::channel_close(rh.handle));
        expect_eq!(Ok(()), oak::channel_close(wh.handle));
        Ok(())
    }

    fn test_storage_pseudo_node_privilege(&mut self) -> TestResult {
        // Storage pseudo node cannot be created with a non-public label.
        let label = oak_abi::label::confidentiality_label(oak_abi::label::tls_endpoint_tag(
            STORAGE_PROXY_ADDRESS
                .parse::<Uri>()
                .unwrap()
                .authority()
                .unwrap()
                .as_str(),
        ));
        let config = NodeConfiguration {
            config_type: Some(ConfigType::StorageConfig(StorageProxyConfiguration {
                address: STORAGE_PROXY_ADDRESS.to_string(),
            })),
        };
        let (wh, rh) = oak::channel_create("Test", &label).expect("could not create channel");
        expect_eq!(
            Err(OakStatus::ErrPermissionDenied),
            oak::node_create("storage", &config, &label, rh)
        );
        expect_eq!(Ok(()), oak::channel_close(rh.handle));
        expect_eq!(Ok(()), oak::channel_close(wh.handle));
        Ok(())
    }

    fn test_logger_pseudo_node_privilege(&mut self) -> TestResult {
        // Logger pseudo node can be created with a non-public label when the `oak-unsafe` feature
        // is enabled.
        let label = oak_abi::label::confidentiality_label(oak_abi::label::tls_endpoint_tag(
            GRPC_CLIENT_ADDRESS
                .parse::<Uri>()
                .unwrap()
                .authority()
                .unwrap()
                .as_str(),
        ));
        let config = oak::node_config::log();
        let (wh, rh) = oak::channel_create("Test", &label).expect("could not create channel");
        expect_eq!(Ok(()), oak::node_create("logger", &config, &label, rh));
        expect_eq!(Ok(()), oak::channel_close(rh.handle));
        expect_eq!(Ok(()), oak::channel_close(wh.handle));
        Ok(())
    }
}

// Helper for storage error conversion.
fn from_proto(status: oak::grpc::Status) -> Box<dyn std::error::Error> {
    Box::new(std::io::Error::new(
        std::io::ErrorKind::Other,
        format!("status code {} message '{}'", status.code, status.message),
    ))
}

fn lose_channels() {
    // Create a channel holding a message that holds references to itself.
    let (wh, rh) = oak::channel_create("Closed-self-ref", &Label::public_untrusted()).unwrap();
    let data = vec![0x01, 0x02, 0x03];
    oak::channel_write(wh, &data, &[wh.handle, rh.handle]).unwrap();
    // Close both handles so this channel is immediately lost.
    oak::channel_close(wh.handle).unwrap();
    oak::channel_close(rh.handle).unwrap();

    // Create a channel holding a message that holds references to itself.
    let (wh, rh) = oak::channel_create("Lost-self-ref", &Label::public_untrusted()).unwrap();
    let data = vec![0x01, 0x02, 0x03];
    oak::channel_write(wh, &data, &[wh.handle, rh.handle]).unwrap();
    // Keep the write handle open, so this channel will be lost when
    // the Node exits
    oak::channel_close(rh.handle).unwrap();

    // Create a pair of channels, each holding a message that holds references to the other
    let (wh_a, rh_a) =
        oak::channel_create("Closed-cross-ref-channel-a", &Label::public_untrusted()).unwrap();
    let (wh_b, rh_b) =
        oak::channel_create("Closed-cross-ref-channel-b", &Label::public_untrusted()).unwrap();
    oak::channel_write(wh_a, &data, &[wh_b.handle, rh_b.handle]).unwrap();
    oak::channel_write(wh_b, &data, &[wh_a.handle, rh_a.handle]).unwrap();
    // Close all handles so these channels are immediately lost.
    oak::channel_close(wh_a.handle).unwrap();
    oak::channel_close(wh_b.handle).unwrap();
    oak::channel_close(rh_a.handle).unwrap();
    oak::channel_close(rh_b.handle).unwrap();

    // Create a pair of channels, each holding a message that holds references to the other
    let (wh_a, rh_a) =
        oak::channel_create("Lost-cross-ref-channel-a", &Label::public_untrusted()).unwrap();
    let (wh_b, rh_b) =
        oak::channel_create("Lost-cross-ref-channel-b", &Label::public_untrusted()).unwrap();
    oak::channel_write(wh_a, &data, &[wh_b.handle, rh_b.handle]).unwrap();
    oak::channel_write(wh_b, &data, &[wh_a.handle, rh_a.handle]).unwrap();
    // Keep the write handles open.
    oak::channel_close(rh_a.handle).unwrap();
    oak::channel_close(rh_b.handle).unwrap();

    // Node exit: at this point the Runtime can recover channels that are still in
    // the Node's handle table.
}

// Entrypoint for a Node instance that creates channels and loses track of them.
#[no_mangle]
pub extern "C" fn channel_loser(_handle: u64) {
    lose_channels();
    // At this point there are two channels that this Node can no longer access.
    // On Node exit (when this function returns), the Runtime should free those
    // channels.
}

// Entrypoint for a Node instance that handles HTTP requests.
#[no_mangle]
pub extern "C" fn http_oak_main(http_channel: u64) {
    let log_sender = oak::logger::create().unwrap();
    oak::logger::init(log_sender, log::Level::Debug).unwrap();
    let handler = http_server::StaticHttpHandler;
    oak::run_command_loop(
        handler,
        Receiver::new(oak_io::handle::ReadHandle {
            handle: http_channel,
        })
        .iter(),
    );
}

// Build a nested chain of channels where:
//  - The innermost channel has a message with data (0x8 0xC) in it.
//  - The next channel has a message with a single read handle in it; this is the only handle for
//    the previous channel that exists.
//  - The next channel has a message with a single read handle in it; this is the only handle for
//    the previous channel that exists.
//  - ...
//  - The final channel has a message with a single read handle in it; this is the only handle for
//    the previous channel that exists.
// All of the channels and the embedded data can be recovered from the read
// handle of the final data. Alternatively, all of them should be freed by
// the runtime when the final handle is closed.
fn new_channel_chain(nest_count: u32) -> Result<oak::ReadHandle, Box<dyn std::error::Error>> {
    // Set up a channel with a message in it.
    let (innermost_wh, innermost_rh) =
        oak::channel_create("Innermost", &Label::public_untrusted()).unwrap();
    let data = vec![0x08, 0x0c];
    expect_eq!(Ok(()), oak::channel_write(innermost_wh, &data, &[]));
    expect_eq!(Ok(()), oak::channel_close(innermost_wh.handle));

    let mut inner_rh = innermost_rh;
    for _ in 0..nest_count {
        // Put a message with a handle to the previous channel into a new outer channel.
        let (outer_wh, outer_rh) =
            oak::channel_create("Outer", &Label::public_untrusted()).unwrap();
        expect_eq!(
            Ok(()),
            oak::channel_write(outer_wh, &[], &[inner_rh.handle])
        );
        expect_eq!(Ok(()), oak::channel_close(inner_rh.handle));
        expect_eq!(Ok(()), oak::channel_close(outer_wh.handle));
        inner_rh = outer_rh;
    }
    Ok(inner_rh)
}

oak::entrypoint!(panic_main<ConfigMap> => |_receiver| {
    panic!("deliberate panic");
});
