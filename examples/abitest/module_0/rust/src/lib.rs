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
use log::{debug, error, info, trace, warn};
use oak::{grpc, ChannelReadStatus, OakError, OakStatus};
use oak_abi::{
    label::Label,
    proto::oak::application::{
        NodeConfiguration, RoughtimeClientConfiguration, StorageProxyConfiguration,
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

struct FrontendNode {
    backend_out: Vec<oak::WriteHandle>,
    backend_in: Vec<oak::ReadHandle>,
    storage: Option<oak::storage::Storage>,
    absent_storage: Option<oak::storage::Storage>,
    storage_name: Vec<u8>,
    grpc_service: Option<OakAbiTestServiceClient>,
    absent_grpc_service: Option<OakAbiTestServiceClient>,
    roughtime: Option<oak::roughtime::Roughtime>,
    misconfigured_roughtime: Option<oak::roughtime::Roughtime>,
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
            let (wh, rh) = oak::channel_create().unwrap();
            oak::node_create(
                &oak::node_config::wasm(FRONTEND_MODULE_NAME, "channel_loser"),
                rh,
            )
            .expect("failed to create channel_loser ephemeral Node");
            oak::channel_close(wh.handle).unwrap();
            oak::channel_close(rh.handle).unwrap();
        }
        oak::logger::init(log::Level::Debug).expect("could not initialize logging node");

        // Create backend node instances.
        let mut backend_out = Vec::with_capacity(BACKEND_COUNT);
        let mut backend_in = Vec::with_capacity(BACKEND_COUNT);
        for i in 0..BACKEND_COUNT {
            let (write_handle, read_handle) =
                oak::channel_create().expect("could not create channel");
            oak::node_create(
                &oak::node_config::wasm(BACKEND_MODULE_NAME, BACKEND_ENTRYPOINT_NAME),
                read_handle,
            )
            .expect("could not create node");
            oak::channel_close(read_handle.handle).expect("could not close channel");
            backend_out.push(write_handle);

            // Create a back channel, and pass the write half to the backend
            // as the first message on the outbound channel.
            let (write_handle, read_handle) =
                oak::channel_create().expect("could not create channel");
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
                address: "https://localhost:7867".to_string(),
            }),
            absent_storage: oak::storage::Storage::new(&StorageProxyConfiguration {
                address: "https://test.invalid:9999".to_string(),
            }),
            storage_name: storage_name.as_bytes().to_vec(),
            grpc_service: oak::grpc::client::Client::new(&oak::node_config::grpc_client(
                "https://localhost:7878",
            ))
            .map(OakAbiTestServiceClient),
            absent_grpc_service: oak::grpc::client::Client::new(&oak::node_config::grpc_client(
                "https://test.invalid:9999",
            ))
            .map(OakAbiTestServiceClient),
            roughtime: oak::roughtime::Roughtime::new(&RoughtimeClientConfiguration {
                ..Default::default()
            }),
            misconfigured_roughtime: oak::roughtime::Roughtime::new(
                &RoughtimeClientConfiguration {
                    min_overlapping_intervals: 99,
                    ..Default::default()
                },
            ),
        }
    }
}

#[no_mangle]
pub extern "C" fn frontend_oak_main(in_handle: u64) {
    let _ = std::panic::catch_unwind(|| {
        oak::set_panic_hook();
        let node = FrontendNode::new();
        let dispatcher = OakAbiTestServiceDispatcher::new(node);
        let in_channel = ::oak::ReadHandle {
            handle: ::oak::Handle::from_raw(in_handle),
        };
        oak::run_event_loop(dispatcher, in_channel);
    });
}

#[no_mangle]
pub extern "C" fn grpc_frontend_oak_main(_in_handle: u64) {
    let _ = std::panic::catch_unwind(|| {
        oak::set_panic_hook();
        let node = FrontendNode::new();
        let dispatcher = OakAbiTestServiceDispatcher::new(node);
        let grpc_channel =
            oak::grpc::server::init("[::]:8080").expect("could not create gRPC server pseudo-Node");
        oak::run_event_loop(dispatcher, grpc_channel);
    });
}

type TestResult = Result<(), Box<dyn std::error::Error>>;
type TestFn = fn(&mut FrontendNode) -> TestResult;

impl OakAbiTestService for FrontendNode {
    fn run_tests(&mut self, req: AbiTestRequest) -> grpc::Result<AbiTestResponse> {
        info!(
            "Run tests matching '{}' except those matching '{}'",
            req.include, req.exclude
        );
        let include = regex::Regex::new(&req.include).unwrap();
        let exclude = regex::Regex::new(&req.exclude).unwrap();
        let mut results = Vec::<proto::abi_test_response::TestResult>::new();

        // Manual registry of all tests.
        let mut tests: HashMap<&str, TestFn> = HashMap::new();
        tests.insert("ChannelCreateRaw", FrontendNode::test_channel_create_raw);
        tests.insert("ChannelCreate", FrontendNode::test_channel_create);
        tests.insert("ChannelCloseRaw", FrontendNode::test_channel_close_raw);
        tests.insert("ChannelClose", FrontendNode::test_channel_close);
        tests.insert("ChannelReadRaw", FrontendNode::test_channel_read_raw);
        tests.insert("ChannelRead", FrontendNode::test_channel_read);
        tests.insert("ChannelReadOrphan", FrontendNode::test_channel_read_orphan);
        tests.insert("ChannelWriteRaw", FrontendNode::test_channel_write_raw);
        tests.insert("ChannelWrite", FrontendNode::test_channel_write);
        tests.insert(
            "ChannelWriteHandle",
            FrontendNode::test_channel_write_handle,
        );
        tests.insert(
            "ChannelWriteOrphanEmpty",
            FrontendNode::test_channel_write_orphan_empty,
        );
        tests.insert(
            "ChannelWriteOrphanFull",
            FrontendNode::test_channel_write_orphan_full,
        );
        tests.insert(
            "ChannelHandleRecovered",
            FrontendNode::test_channel_handle_recovered,
        );
        tests.insert("ChannelChainLost", FrontendNode::test_channel_chain_lost);
        tests.insert(
            "ChannelChainRecovered",
            FrontendNode::test_channel_chain_recovered,
        );
        tests.insert("WaitOnChannelsRaw", FrontendNode::test_channel_wait_raw);
        tests.insert("WaitOnChannels", FrontendNode::test_channel_wait);
        tests.insert(
            "WaitOnChannelsOrphan",
            FrontendNode::test_channel_wait_orphan,
        );
        tests.insert("NodeCreate", FrontendNode::test_node_create);
        tests.insert("NodeCreateRaw", FrontendNode::test_node_create_raw);
        tests.insert("RandomGetRaw", FrontendNode::test_random_get_raw);
        tests.insert("RandomGet", FrontendNode::test_random_get);
        tests.insert("RandomRng", FrontendNode::test_random_rng);
        tests.insert(
            "ChannelHandleReuse",
            FrontendNode::test_channel_handle_reuse,
        );
        tests.insert("Log", FrontendNode::test_log);
        tests.insert("DirectLog", FrontendNode::test_direct_log);
        tests.insert("BackendRoundtrip", FrontendNode::test_backend_roundtrip);
        tests.insert("Storage", FrontendNode::test_storage);
        tests.insert("AbsentStorage", FrontendNode::test_absent_storage);
        tests.insert(
            "GrpcClientUnaryMethod",
            FrontendNode::test_grpc_client_unary_method,
        );
        tests.insert(
            "GrpcClientServerStreamingMethod",
            FrontendNode::test_grpc_client_server_streaming_method,
        );
        tests.insert("AbsentGrpcClient", FrontendNode::test_absent_grpc_client);
        tests.insert("RoughtimeClient", FrontendNode::test_roughtime_client);
        tests.insert(
            "MisconfiguredRoughtimeClient",
            FrontendNode::test_roughtime_client_misconfig,
        );

        for (&name, &testfn) in &tests {
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
            let mut result = proto::abi_test_response::TestResult::default();
            result.name = name.to_string();
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

        let mut res = AbiTestResponse::default();
        res.results = results;

        Ok(res)
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
                combined_text.push_str(&ok_text);
            }
        }
        info!("client_streaming_method -> Ok({})", combined_text);
        let mut rsp = GrpcTestResponse::default();
        rsp.text = combined_text;
        Ok(rsp)
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
                    let mut rsp = GrpcTestResponse::default();
                    rsp.text = ok_text.to_string();
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
    let label_bytes = Label::public_untrusted().serialize();
    let result = unsafe {
        oak_abi::channel_create(
            &mut w as *mut u64,
            &mut r as *mut u64,
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
        let label_bytes = Label::public_untrusted().serialize();
        expect_eq!(OakStatus::ErrInvalidArgs as u32, unsafe {
            oak_abi::channel_create(
                invalid_raw_offset(),
                &mut read as *mut u64,
                label_bytes.as_ptr(),
                label_bytes.len(),
            )
        });
        expect_eq!(OakStatus::ErrInvalidArgs as u32, unsafe {
            oak_abi::channel_create(
                &mut write as *mut u64,
                invalid_raw_offset(),
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
            match oak::channel_create() {
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
        let (w, r) = oak::channel_create().unwrap();
        expect_eq!(Ok(()), oak::channel_close(w.handle));
        expect_eq!(Ok(()), oak::channel_close(r.handle));
        expect_eq!(Err(OakStatus::ErrBadHandle), oak::channel_close(w.handle));
        expect_eq!(
            Err(OakStatus::ErrBadHandle),
            oak::channel_close(oak::Handle::from_raw(9_999_999))
        );

        // Can close ends in either order.
        let (w, r) = oak::channel_create().unwrap();
        expect_eq!(Ok(()), oak::channel_close(r.handle));
        expect_eq!(Ok(()), oak::channel_close(w.handle));
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
        let (out_channel, in_channel) = oak::channel_create().unwrap();

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
        let bogus_channel = oak::ReadHandle {
            handle: oak::Handle::from_raw(99999),
        };
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
        let (out_channel, in_channel) = oak::channel_create().unwrap();

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
        let (out_channel, in_channel) = oak::channel_create().unwrap();

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
        let bogus_channel = oak::WriteHandle {
            handle: oak::Handle::from_raw(99999),
        };
        expect_eq!(
            Err(OakStatus::ErrBadHandle),
            oak::channel_write(bogus_channel, &data, &[])
        );

        expect_eq!(Ok(()), oak::channel_close(in_channel.handle));
        expect_eq!(Ok(()), oak::channel_close(out_channel.handle));
        Ok(())
    }

    fn test_channel_write_handle(&mut self) -> TestResult {
        let (out_channel, in_channel) = oak::channel_create().unwrap();

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

        expect_eq!(Ok(()), oak::channel_close(in_channel.handle));
        expect_eq!(Ok(()), oak::channel_close(out_channel.handle));
        Ok(())
    }

    fn test_channel_write_orphan_empty(&mut self) -> TestResult {
        let (out_channel, in_channel) = oak::channel_create().unwrap();

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
        let (out_channel, in_channel) = oak::channel_create().unwrap();

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
        let (lost_wh, lost_rh) = oak::channel_create().unwrap();
        let data = vec![0x08, 0x0c];
        expect_eq!(Ok(()), oak::channel_write(lost_wh, &data, &[]));

        // Put a message with handle to the first channel into a second channel.
        let (holder_wh, holder_rh) = oak::channel_create().unwrap();
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
                OakStatus::ErrBadHandle as u32,
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
        let (out1, in1) = oak::channel_create().unwrap();
        let (out2, in2) = oak::channel_create().unwrap();

        // Waiting on (just) non-read channel handles should fail immediately.
        expect_eq!(
            Err(OakStatus::ErrBadHandle),
            oak::wait_on_channels(&[
                oak::ReadHandle {
                    handle: out1.handle
                },
                oak::ReadHandle {
                    handle: oak::Handle::from_raw(9_999_999)
                }
            ])
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
                oak::ReadHandle {
                    handle: oak::Handle::from_raw(9_999_999)
                }
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
        let (out1, in1) = oak::channel_create().unwrap();
        let (out2, in2) = oak::channel_create().unwrap();

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

    fn test_node_create_raw(&mut self) -> TestResult {
        let (_, in_channel, _) = channel_create_raw();

        let valid_label_bytes = Label::public_untrusted().serialize();

        // This sequence of bytes should not deserialize as a [`oak_abi::proto::policy::Label`] or
        // [`oak_abi::proto::oak::application::NodeConfiguration`] protobuf. We make sure
        // here that this continues to be the case by making sure that [`Label::decode`] and
        // [`NodeConfiguration::decode`] fail to parse these bytes.
        let invalid_proto_bytes = vec![0, 88, 0];
        assert_eq!(false, Label::decode(invalid_proto_bytes.as_ref()).is_ok());
        assert_eq!(
            false,
            NodeConfiguration::decode(invalid_proto_bytes.as_ref()).is_ok()
        );

        {
            let mut config_bytes = Vec::new();
            oak::node_config::wasm(BACKEND_MODULE_NAME, BACKEND_ENTRYPOINT_NAME)
                .encode(&mut config_bytes)?;
            expect_eq!(OakStatus::Ok as u32, unsafe {
                oak_abi::node_create(
                    config_bytes.as_ptr(),
                    config_bytes.len(),
                    valid_label_bytes.as_ptr(),
                    valid_label_bytes.len(),
                    in_channel,
                )
            });
        }

        {
            let mut config_bytes = Vec::new();
            oak::node_config::wasm(BACKEND_MODULE_NAME, BACKEND_ENTRYPOINT_NAME)
                .encode(&mut config_bytes)?;
            expect_eq!(OakStatus::ErrInvalidArgs as u32, unsafe {
                oak_abi::node_create(
                    config_bytes.as_ptr(),
                    config_bytes.len(),
                    invalid_proto_bytes.as_ptr(),
                    invalid_proto_bytes.len(),
                    in_channel,
                )
            });
        }

        {
            expect_eq!(OakStatus::ErrInvalidArgs as u32, unsafe {
                oak_abi::node_create(
                    invalid_raw_offset() as *mut u8,
                    1,
                    valid_label_bytes.as_ptr(),
                    valid_label_bytes.len(),
                    in_channel,
                )
            });
        }

        {
            expect_eq!(OakStatus::ErrInvalidArgs as u32, unsafe {
                oak_abi::node_create(
                    invalid_proto_bytes.as_ptr(),
                    invalid_proto_bytes.len(),
                    valid_label_bytes.as_ptr(),
                    valid_label_bytes.len(),
                    in_channel,
                )
            });
        }

        Ok(())
    }
    fn test_node_create(&mut self) -> TestResult {
        expect_eq!(
            Err(OakStatus::ErrInvalidArgs),
            oak::node_create(
                &oak::node_config::wasm("no_such_module", BACKEND_ENTRYPOINT_NAME),
                self.backend_in[0]
            )
        );
        expect_eq!(
            Err(OakStatus::ErrInvalidArgs),
            oak::node_create(
                &oak::node_config::wasm(BACKEND_MODULE_NAME, "no_such_entrypoint"),
                self.backend_in[0]
            )
        );
        expect_eq!(
            Err(OakStatus::ErrInvalidArgs),
            oak::node_create(
                &oak::node_config::wasm(
                    BACKEND_MODULE_NAME,
                    "backend_fake_main" /* exists but wrong signature */
                ),
                self.backend_in[0]
            )
        );
        expect_eq!(
            Err(OakStatus::ErrBadHandle),
            oak::node_create(
                &oak::node_config::wasm(BACKEND_MODULE_NAME, BACKEND_ENTRYPOINT_NAME),
                oak::ReadHandle {
                    handle: oak::Handle::from_raw(oak_abi::INVALID_HANDLE)
                }
            )
        );
        let (out_handle, in_handle) = oak::channel_create().unwrap();
        expect_eq!(
            Ok(()),
            oak::node_create(
                &oak::node_config::wasm(BACKEND_MODULE_NAME, BACKEND_ENTRYPOINT_NAME),
                in_handle
            )
        );
        expect_eq!(
            Ok(()),
            oak::node_create(
                &oak::node_config::wasm(BACKEND_MODULE_NAME, BACKEND_ENTRYPOINT_NAME),
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
        let (out_handle, in_handle) = oak::channel_create().unwrap();
        let data = vec![0x01, 0x02, 0x03];
        expect_eq!(Ok(()), oak::channel_write(out_handle, &data, &[]));

        // Read from an invalid handle.
        let mut buffer = Vec::<u8>::with_capacity(5);
        let mut handles = Vec::with_capacity(5);
        expect_eq!(
            Err(OakStatus::ErrBadHandle),
            oak::channel_read(
                oak::ReadHandle {
                    handle: oak::Handle::from_raw(9_987_123)
                },
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
            oak::wait_on_channels(&[
                in_handle,
                oak::ReadHandle {
                    handle: oak::Handle::from_raw(9_987_321)
                }
            ])
        );

        // Close both of the previously mentioned invalid handles.
        expect_eq!(
            Err(OakStatus::ErrBadHandle),
            oak::channel_close(oak::Handle::from_raw(9_987_123))
        );
        expect_eq!(
            Err(OakStatus::ErrBadHandle),
            oak::channel_close(oak::Handle::from_raw(9_987_321))
        );

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
        let (logging_handle, read_handle) =
            oak::channel_create().expect("could not create channel");
        oak::node_create(&oak::node_config::log(), read_handle).expect("could not create node");
        oak::channel_close(read_handle.handle).expect("could not close channel");

        expect!(logging_handle.handle.is_valid());
        let (out_handle, in_handle) = oak::channel_create().expect("could not create channel");

        oak::channel_write(
            logging_handle,
            "Malformed message sent direct to logging channel!".as_bytes(),
            &[in_handle.handle, out_handle.handle],
        )
        .expect("could not write to channel");

        let mut bytes = Vec::new();
        oak_abi::proto::oak::log::LogMessage {
            level: oak_abi::proto::oak::log::Level::Info as i32,
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
            let (new_write, new_read) = oak::channel_create().unwrap();
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
            let mut new_in_channel = oak::ReadHandle {
                handle: oak::Handle::from_raw(0),
            };
            for (j, ready) in readies.iter().enumerate() {
                if *ready == ChannelReadStatus::ReadReady {
                    info!("got response from backend[{}]", j);
                    expect_eq!(oak::Handle::from_raw(0), new_in_channel.handle);
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
    fn test_grpc_client_unary_method(&mut self) -> TestResult {
        let grpc_stub = self.grpc_service.as_ref().ok_or_else(|| {
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
        let grpc_stub = self.grpc_service.as_ref().ok_or_else(|| {
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
    fn test_absent_grpc_client(&mut self) -> TestResult {
        // Expect to have a channel to a gRPC client pseudo-Node, but the remote
        // gRPC service is unavailable.
        let grpc_stub = self.absent_grpc_service.as_ref().ok_or_else(|| {
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

        // Attempting to invoke any sort of method should fail.
        let result = grpc_stub.unary_method(req.clone());
        info!("absent.unary_method() -> {:?}", result);
        expect_matches!(result, Err(_));

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
    let (wh, rh) = oak::channel_create().unwrap();
    let data = vec![0x01, 0x02, 0x03];
    oak::channel_write(wh, &data, &[wh.handle, rh.handle]).unwrap();
    // Close both handles so this channel is immediately lost.
    oak::channel_close(wh.handle).unwrap();
    oak::channel_close(rh.handle).unwrap();

    // Create a channel holding a message that holds references to itself.
    let (wh, rh) = oak::channel_create().unwrap();
    let data = vec![0x01, 0x02, 0x03];
    oak::channel_write(wh, &data, &[wh.handle, rh.handle]).unwrap();
    // Keep the write handle open, so this channel will be lost when
    // the Node exits
    oak::channel_close(rh.handle).unwrap();

    // Create a pair of channels, each holding a message that holds references to the other
    let (wh_a, rh_a) = oak::channel_create().unwrap();
    let (wh_b, rh_b) = oak::channel_create().unwrap();
    oak::channel_write(wh_a, &data, &[wh_b.handle, rh_b.handle]).unwrap();
    oak::channel_write(wh_b, &data, &[wh_a.handle, rh_a.handle]).unwrap();
    // Close all handles so these channels are immediately lost.
    oak::channel_close(wh_a.handle).unwrap();
    oak::channel_close(wh_b.handle).unwrap();
    oak::channel_close(rh_a.handle).unwrap();
    oak::channel_close(rh_b.handle).unwrap();

    // Create a pair of channels, each holding a message that holds references to the other
    let (wh_a, rh_a) = oak::channel_create().unwrap();
    let (wh_b, rh_b) = oak::channel_create().unwrap();
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
    let (innermost_wh, innermost_rh) = oak::channel_create().unwrap();
    let data = vec![0x08, 0x0c];
    expect_eq!(Ok(()), oak::channel_write(innermost_wh, &data, &[]));
    expect_eq!(Ok(()), oak::channel_close(innermost_wh.handle));

    let mut inner_rh = innermost_rh;
    for _ in 0..nest_count {
        // Put a message with a handle to the previous channel into a new outer channel.
        let (outer_wh, outer_rh) = oak::channel_create().unwrap();
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
