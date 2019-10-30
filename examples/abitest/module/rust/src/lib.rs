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

extern crate abitest_common;
extern crate byteorder;
#[macro_use]
extern crate expect;
#[macro_use]
extern crate log;
extern crate oak;
extern crate oak_log;
extern crate protobuf;
extern crate rand;
extern crate regex;
extern crate serde;

mod proto;

use abitest_common::InternalMessage;
use byteorder::WriteBytesExt;
use oak::grpc::OakNode;
use oak::{grpc, ChannelReadStatus, OakStatus};
use proto::abitest::{ABITestRequest, ABITestResponse, ABITestResponse_TestResult};
use proto::abitest_grpc::{dispatch, OakABITestServiceNode};
use protobuf::ProtobufEnum;
use rand::Rng;
use std::collections::HashMap;
use std::io::Write;

const BACKEND_COUNT: usize = 3;
struct FrontendNode {
    grpc_in: oak::ReadHandle,
    backend_out: [oak::WriteHandle; BACKEND_COUNT],
    backend_in: [oak::ReadHandle; BACKEND_COUNT],
}

#[no_mangle]
pub extern "C" fn oak_main() -> i32 {
    match std::panic::catch_unwind(|| {
        let node = FrontendNode::new();
        let grpc_in = node.grpc_in;
        oak::grpc::event_loop(node, grpc_in)
    }) {
        Ok(rc) => rc,
        Err(_) => OakStatus::ERR_INTERNAL.value(),
    }
}

impl oak::grpc::OakNode for FrontendNode {
    fn new() -> Self {
        oak_log::init(
            log::Level::Debug,
            oak::WriteHandle {
                handle: oak::channel_find("logging_port"),
            },
        )
        .unwrap();
        FrontendNode {
            grpc_in: oak::ReadHandle {
                handle: oak::channel_find("gRPC_input"),
            },
            backend_out: [
                oak::WriteHandle {
                    handle: oak::channel_find("to_backend_0"),
                },
                oak::WriteHandle {
                    handle: oak::channel_find("to_backend_1"),
                },
                oak::WriteHandle {
                    handle: oak::channel_find("to_backend_2"),
                },
            ],
            backend_in: [
                oak::ReadHandle {
                    handle: oak::channel_find("from_backend_0"),
                },
                oak::ReadHandle {
                    handle: oak::channel_find("from_backend_1"),
                },
                oak::ReadHandle {
                    handle: oak::channel_find("from_backend_2"),
                },
            ],
        }
    }
    fn invoke(&mut self, method: &str, req: &[u8], writer: grpc::ChannelResponseWriter) {
        dispatch(self, method, req, writer)
    }
}

impl OakABITestServiceNode for FrontendNode {
    fn run_tests(&mut self, req: ABITestRequest) -> grpc::Result<ABITestResponse> {
        info!("Run tests matching {}", req.filter);
        let filter = regex::Regex::new(&req.filter).unwrap();
        let mut results = protobuf::RepeatedField::<ABITestResponse_TestResult>::new();

        // Manual registry of all tests.
        type TestFn = fn(&FrontendNode) -> std::io::Result<()>;
        let mut tests: HashMap<&str, TestFn> = HashMap::new();
        tests.insert("ChannelFindRaw", FrontendNode::test_channel_find_raw);
        tests.insert("ChannelFind", FrontendNode::test_channel_find);
        tests.insert("ChannelCreateRaw", FrontendNode::test_channel_create_raw);
        tests.insert("ChannelCreate", FrontendNode::test_channel_create);
        tests.insert("ChannelCloseRaw", FrontendNode::test_channel_close_raw);
        tests.insert("ChannelClose", FrontendNode::test_channel_close);
        tests.insert("ChannelReadRaw", FrontendNode::test_channel_read_raw);
        tests.insert("ChannelRead", FrontendNode::test_channel_read);
        tests.insert("ChannelWriteRaw", FrontendNode::test_channel_write_raw);
        tests.insert("ChannelWrite", FrontendNode::test_channel_write);
        tests.insert("WaitOnChannelsRaw", FrontendNode::test_channel_wait_raw);
        tests.insert("WaitOnChannels", FrontendNode::test_channel_wait);
        tests.insert("RandomGetRaw", FrontendNode::test_random_get_raw);
        tests.insert("RandomGet", FrontendNode::test_random_get);
        tests.insert("RandomRng", FrontendNode::test_random_rng);
        tests.insert(
            "ChannelHandleReuse",
            FrontendNode::test_channel_handle_reuse,
        );
        tests.insert("BackendRoundtrip", FrontendNode::test_backend_roundtrip);

        for (&name, &testfn) in &tests {
            if !filter.is_match(name) {
                continue;
            }
            info!("running test {}", name);
            let mut result = ABITestResponse_TestResult::new();
            result.set_name(name.to_string());
            match testfn(self) {
                Ok(()) => result.set_success(true),
                Err(err) => {
                    result.set_success(false);
                    result.set_details(format!("Error: {}", err));
                }
            }
            results.push(result);
        }

        let mut res = ABITestResponse::new();
        res.set_results(results);
        Ok(res)
    }
}

// Helper for status conversion
fn status_convert<T>(result: Result<T, OakStatus>) -> std::io::Result<T> {
    match result {
        Ok(t) => Ok(t),
        Err(status) => Err(std::io::Error::new(
            std::io::ErrorKind::Other,
            format!("failure {:?}", status),
        )),
    }
}

// Return an offset value that is beyond the bounds of available linear memory.
fn invalid_raw_offset() -> *mut u64 {
    // Currently no way to get at the `memory.size` Wasm instruction from Rust,
    // so pick a large number instead.
    0x7fff_fff0 as *mut u64
}

impl FrontendNode {
    fn test_channel_find_raw(&self) -> std::io::Result<()> {
        unsafe {
            expect_eq!(
                0,
                oak::wasm::channel_find(invalid_raw_offset() as *const u8, 2)
            );
        }
        Ok(())
    }

    fn test_channel_find(&self) -> std::io::Result<()> {
        // Idempotent result.
        expect_eq!(self.grpc_in.handle, oak::channel_find("gRPC_input"));
        expect_eq!(
            self.backend_out[0].handle,
            oak::channel_find("to_backend_0")
        );
        expect_eq!(
            self.backend_in[0].handle,
            oak::channel_find("from_backend_0")
        );
        // Whitespace is significant.
        expect_eq!(0, oak::channel_find(" gRPC_input"));
        expect_eq!(0, oak::channel_find(" gRPC_input "));
        expect_eq!(0, oak::channel_find("bogus"));
        expect_eq!(0, oak::channel_find(""));
        Ok(())
    }

    fn test_channel_create_raw(&self) -> std::io::Result<()> {
        let mut write = oak::WriteHandle { handle: 0 };
        let mut read = oak::ReadHandle { handle: 0 };
        unsafe {
            expect_eq!(
                OakStatus::ERR_INVALID_ARGS.value() as u32,
                oak::wasm::channel_create(
                    invalid_raw_offset() as *mut u64,
                    &mut read.handle as *mut u64
                )
            );
            expect_eq!(
                OakStatus::ERR_INVALID_ARGS.value() as u32,
                oak::wasm::channel_create(
                    &mut write.handle as *mut u64,
                    invalid_raw_offset() as *mut u64
                )
            );
        }
        Ok(())
    }

    fn test_channel_create(&self) -> std::io::Result<()> {
        let mut handles = Vec::<(oak::WriteHandle, oak::ReadHandle)>::new();
        for _i in 0..500 {
            match oak::channel_create() {
                Ok(pair) => handles.push(pair),
                Err(status) => {
                    return Err(std::io::Error::new(
                        std::io::ErrorKind::Other,
                        format!("channel_create failure {:?}", status),
                    ));
                }
            }
        }
        for (w, r) in handles {
            expect_eq!(OakStatus::OK, oak::channel_close(r.handle));
            expect_eq!(OakStatus::OK, oak::channel_close(w.handle));
        }
        Ok(())
    }

    fn test_channel_close_raw(&self) -> std::io::Result<()> {
        let (w, r) = oak::channel_create().unwrap();
        unsafe {
            expect_eq!(
                OakStatus::OK.value() as u32,
                oak::wasm::channel_close(w.handle)
            );
            expect_eq!(
                OakStatus::OK.value() as u32,
                oak::wasm::channel_close(r.handle)
            );
            expect_eq!(
                OakStatus::ERR_BAD_HANDLE.value() as u32,
                oak::wasm::channel_close(w.handle)
            );
            expect_eq!(
                OakStatus::ERR_BAD_HANDLE.value() as u32,
                oak::wasm::channel_close(9_999_999)
            );
        }
        Ok(())
    }

    fn test_channel_close(&self) -> std::io::Result<()> {
        let (w, r) = oak::channel_create().unwrap();
        expect_eq!(OakStatus::OK, oak::channel_close(w.handle));
        expect_eq!(OakStatus::OK, oak::channel_close(r.handle));
        expect_eq!(OakStatus::ERR_BAD_HANDLE, oak::channel_close(w.handle));
        expect_eq!(OakStatus::ERR_BAD_HANDLE, oak::channel_close(9_999_999));

        // Can close ends in either order.
        let (w, r) = oak::channel_create().unwrap();
        expect_eq!(OakStatus::OK, oak::channel_close(r.handle));
        expect_eq!(OakStatus::OK, oak::channel_close(w.handle));
        Ok(())
    }

    fn test_channel_read_raw(&self) -> std::io::Result<()> {
        let (out_channel, in_channel) = oak::channel_create().unwrap();
        let mut buf = Vec::<u8>::with_capacity(5);
        let mut handles = Vec::with_capacity(5);
        let mut actual_size: u32 = 99;
        let mut actual_handle_count: u32 = 99;
        unsafe {
            // Try invalid values for the 4 linear memory offset arguments.
            expect_eq!(
                OakStatus::ERR_INVALID_ARGS.value() as u32,
                oak::wasm::channel_read(
                    in_channel.handle,
                    invalid_raw_offset() as *mut u8,
                    1,
                    &mut actual_size,
                    handles.as_mut_ptr() as *mut u8,
                    handles.capacity() as u32,
                    &mut actual_handle_count
                )
            );
            expect_eq!(
                OakStatus::ERR_INVALID_ARGS.value() as u32,
                oak::wasm::channel_read(
                    in_channel.handle,
                    buf.as_mut_ptr(),
                    buf.capacity(),
                    invalid_raw_offset() as *mut u32,
                    handles.as_mut_ptr() as *mut u8,
                    handles.capacity() as u32,
                    &mut actual_handle_count
                )
            );
            expect_eq!(
                OakStatus::ERR_INVALID_ARGS.value() as u32,
                oak::wasm::channel_read(
                    in_channel.handle,
                    buf.as_mut_ptr(),
                    buf.capacity(),
                    &mut actual_size,
                    invalid_raw_offset() as *mut u8,
                    1,
                    &mut actual_handle_count
                )
            );
            expect_eq!(
                OakStatus::ERR_INVALID_ARGS.value() as u32,
                oak::wasm::channel_read(
                    in_channel.handle,
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
                OakStatus::OK.value() as u32,
                oak::wasm::channel_read(
                    in_channel.handle,
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
        expect_eq!(OakStatus::OK, oak::channel_close(out_channel.handle));
        expect_eq!(OakStatus::OK, oak::channel_close(in_channel.handle));
        Ok(())
    }

    fn test_channel_read(&self) -> std::io::Result<()> {
        let (out_channel, in_channel) = oak::channel_create().unwrap();

        let mut buffer = Vec::<u8>::with_capacity(5);
        let mut handles = Vec::with_capacity(5);
        expect_eq!(
            OakStatus::OK,
            oak::channel_read(in_channel, &mut buffer, &mut handles)
        );
        expect_eq!(0, buffer.len());
        expect_eq!(0, handles.len());

        // Single message.
        let data = vec![0x01, 0x02, 0x03];
        expect_eq!(OakStatus::OK, oak::channel_write(out_channel, &data, &[]));
        expect_eq!(
            OakStatus::OK,
            oak::channel_read(in_channel, &mut buffer, &mut handles)
        );
        expect_eq!(3, buffer.len());
        expect_eq!(0, handles.len());

        // Reading again zeroes the vector length.
        expect_eq!(
            OakStatus::OK,
            oak::channel_read(in_channel, &mut buffer, &mut handles)
        );
        expect_eq!(0, buffer.len());
        expect_eq!(0, handles.len());
        expect_eq!(5, buffer.capacity());

        // Now send and receive a bigger message.
        let data = vec![0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08];
        expect_eq!(OakStatus::OK, oak::channel_write(out_channel, &data, &[]));
        expect_eq!(
            OakStatus::OK,
            oak::channel_read(in_channel, &mut buffer, &mut handles)
        );
        expect_eq!(8, buffer.len());
        expect_eq!(0, handles.len());
        expect!(buffer.capacity() >= 8);

        // Reading from an invalid handle gives an error.
        let bogus_channel = oak::ReadHandle { handle: 99999 };
        expect_eq!(
            OakStatus::ERR_BAD_HANDLE,
            oak::channel_read(bogus_channel, &mut buffer, &mut handles)
        );

        expect_eq!(OakStatus::OK, oak::channel_close(out_channel.handle));
        expect_eq!(OakStatus::OK, oak::channel_close(in_channel.handle));
        Ok(())
    }

    fn test_channel_write_raw(&self) -> std::io::Result<()> {
        let (out_channel, in_channel) = oak::channel_create().unwrap();

        let buf = vec![0x01];
        let handles = vec![in_channel.handle];
        unsafe {
            expect_eq!(
                OakStatus::ERR_INVALID_ARGS.value() as u32,
                oak::wasm::channel_write(
                    out_channel.handle,
                    invalid_raw_offset() as *const u8,
                    1,
                    handles.as_ptr() as *const u8,
                    handles.len() as u32,
                )
            );
            expect_eq!(
                OakStatus::ERR_INVALID_ARGS.value() as u32,
                oak::wasm::channel_write(
                    out_channel.handle,
                    buf.as_ptr(),
                    buf.len(),
                    invalid_raw_offset() as *const u8,
                    1,
                )
            );
        }
        expect_eq!(OakStatus::OK, oak::channel_close(in_channel.handle));
        expect_eq!(OakStatus::OK, oak::channel_close(out_channel.handle));
        Ok(())
    }

    fn test_channel_write(&self) -> std::io::Result<()> {
        let (out_channel, in_channel) = oak::channel_create().unwrap();

        // Empty message.
        let empty = vec![];
        expect_eq!(OakStatus::OK, oak::channel_write(out_channel, &empty, &[]));

        // Single message.
        let data = vec![0x01, 0x02, 0x03];
        expect_eq!(OakStatus::OK, oak::channel_write(out_channel, &data, &[]));

        // Now send a bigger message.
        let data = vec![0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08];
        expect_eq!(OakStatus::OK, oak::channel_write(out_channel, &data, &[]));

        // Writing to an invalid handle gives an error.
        let bogus_channel = oak::WriteHandle { handle: 99999 };
        expect_eq!(
            OakStatus::ERR_BAD_HANDLE,
            oak::channel_write(bogus_channel, &data, &[])
        );

        // Close the only read handle for the channel.
        expect_eq!(OakStatus::OK, oak::channel_close(in_channel.handle));

        // Can still write to the channel, even though it's not possible to get
        // the message back.
        expect_eq!(
            OakStatus::ERR_CHANNEL_CLOSED,
            oak::channel_write(out_channel, &data, &[])
        );

        expect_eq!(OakStatus::OK, oak::channel_close(out_channel.handle));
        Ok(())
    }

    fn test_channel_wait_raw(&self) -> std::io::Result<()> {
        let (out_channel, in_channel) = oak::channel_create().unwrap();

        // Write a message to the channel so wait operations don't block.
        let data = vec![0x01, 0x02, 0x03];
        expect_eq!(OakStatus::OK, oak::channel_write(out_channel, &data, &[]));

        unsafe {
            expect_eq!(
                OakStatus::ERR_INVALID_ARGS.value() as u32,
                oak::wasm::wait_on_channels(invalid_raw_offset() as *mut u8, 1)
            );
        }

        unsafe {
            // Wait on [write handle, ready read handle, empty read handle].
            const COUNT: usize = 3;
            let mut space = Vec::with_capacity(COUNT * oak::wasm::SPACE_BYTES_PER_HANDLE);
            space
                .write_u64::<byteorder::LittleEndian>(out_channel.handle)
                .unwrap();
            space.push(0x00);
            space
                .write_u64::<byteorder::LittleEndian>(in_channel.handle)
                .unwrap();
            space.push(0x00);
            space
                .write_u64::<byteorder::LittleEndian>(self.backend_in[0].handle)
                .unwrap();
            space.push(0x99); // deliberate nonsense status value
            expect_eq!(
                OakStatus::OK.value() as u32,
                oak::wasm::wait_on_channels(space.as_mut_ptr(), COUNT as u32)
            );
            expect_eq!(
                ChannelReadStatus::INVALID_CHANNEL.value(),
                i32::from(space[8])
            );
            expect_eq!(
                ChannelReadStatus::READ_READY.value(),
                i32::from(space[9 + 8])
            );
            expect_eq!(
                ChannelReadStatus::NOT_READY.value(),
                i32::from(space[9 + 9 + 8])
            );
        }

        unsafe {
            // Wait on [nonsense handle, read handle].
            const COUNT: usize = 2;
            let mut space = Vec::with_capacity(COUNT * oak::wasm::SPACE_BYTES_PER_HANDLE);
            space
                .write_u64::<byteorder::LittleEndian>(9_123_456)
                .unwrap();
            space.push(0x00);
            space
                .write_u64::<byteorder::LittleEndian>(in_channel.handle)
                .unwrap();
            space.push(0x00);
            expect_eq!(
                OakStatus::OK.value() as u32,
                oak::wasm::wait_on_channels(space.as_mut_ptr(), COUNT as u32)
            );
            expect_eq!(
                oak::proto::oak_api::ChannelReadStatus::INVALID_CHANNEL.value(),
                i32::from(space[8])
            );
            expect_eq!(
                oak::proto::oak_api::ChannelReadStatus::READ_READY.value(),
                i32::from(space[9 + 8])
            );
        }

        expect_eq!(OakStatus::OK, oak::channel_close(out_channel.handle));

        // Still a pending message on in_channel even though the only write half for
        // the channel is closed.
        unsafe {
            const COUNT: usize = 1;
            let mut space = Vec::with_capacity(COUNT * oak::wasm::SPACE_BYTES_PER_HANDLE);
            space
                .write_u64::<byteorder::LittleEndian>(in_channel.handle)
                .unwrap();
            space.push(0x00);
            expect_eq!(
                OakStatus::OK.value() as u32,
                oak::wasm::wait_on_channels(space.as_mut_ptr(), COUNT as u32)
            );
            expect_eq!(
                oak::proto::oak_api::ChannelReadStatus::READ_READY.value(),
                i32::from(space[8])
            );
        }
        // Consume the pending message.
        let mut buffer = Vec::<u8>::with_capacity(5);
        let mut handles = Vec::with_capacity(5);
        expect_eq!(
            OakStatus::OK,
            oak::channel_read(in_channel, &mut buffer, &mut handles)
        );
        expect_eq!(3, buffer.len());
        expect_eq!(0, handles.len());

        // Read half is now orphaned (no pending message, no possible writers).
        unsafe {
            const COUNT: usize = 1;
            let mut space = Vec::with_capacity(COUNT * oak::wasm::SPACE_BYTES_PER_HANDLE);
            space
                .write_u64::<byteorder::LittleEndian>(in_channel.handle)
                .unwrap();
            space.push(0x00);
            expect_eq!(
                OakStatus::ERR_BAD_HANDLE.value() as u32,
                oak::wasm::wait_on_channels(space.as_mut_ptr(), COUNT as u32)
            );
            expect_eq!(
                oak::proto::oak_api::ChannelReadStatus::ORPHANED.value(),
                i32::from(space[8])
            );
        }

        expect_eq!(OakStatus::OK, oak::channel_close(in_channel.handle));
        Ok(())
    }

    fn test_channel_wait(&self) -> std::io::Result<()> {
        // Consume a lot of channel handles before we start, to ensure we're
        // working with handles that don't fit in a single byte.
        self.test_channel_create()?;

        let (out1, in1) = oak::channel_create().unwrap();
        let (out2, in2) = oak::channel_create().unwrap();

        // Waiting on (just) non-read channel handles should fail immediately.
        expect_eq!(
            Err(OakStatus::ERR_BAD_HANDLE),
            oak::wait_on_channels(&[
                oak::ReadHandle {
                    handle: out1.handle
                },
                oak::ReadHandle { handle: 9_999_999 }
            ])
        );

        // Set up first channel with a pending message.
        let data = vec![0x01, 0x02, 0x03];
        expect_eq!(OakStatus::OK, oak::channel_write(out1, &data, &[]));

        expect_eq!(
            vec![ChannelReadStatus::READ_READY, ChannelReadStatus::NOT_READY],
            status_convert(oak::wait_on_channels(&[in1, in2]))?
        );
        // No read so still ready (level triggered not edge triggered).
        expect_eq!(
            vec![ChannelReadStatus::READ_READY, ChannelReadStatus::NOT_READY],
            status_convert(oak::wait_on_channels(&[in1, in2]))?
        );

        expect_eq!(OakStatus::OK, oak::channel_write(out2, &data, &[]));
        expect_eq!(
            vec![ChannelReadStatus::READ_READY, ChannelReadStatus::READ_READY],
            status_convert(oak::wait_on_channels(&[in1, in2]))?
        );

        let mut buffer = Vec::<u8>::with_capacity(5);
        let mut handles = Vec::with_capacity(5);
        expect_eq!(
            OakStatus::OK,
            oak::channel_read(in1, &mut buffer, &mut handles)
        );
        expect_eq!(3, buffer.len());
        expect_eq!(0, handles.len());

        expect_eq!(
            vec![ChannelReadStatus::NOT_READY, ChannelReadStatus::READ_READY],
            status_convert(oak::wait_on_channels(&[in1, in2]))?
        );

        // Write channels and nonsense handles are ignored.
        expect_eq!(
            vec![
                ChannelReadStatus::NOT_READY,
                ChannelReadStatus::READ_READY,
                ChannelReadStatus::INVALID_CHANNEL
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
                ChannelReadStatus::NOT_READY,
                ChannelReadStatus::READ_READY,
                ChannelReadStatus::INVALID_CHANNEL
            ],
            status_convert(oak::wait_on_channels(&[
                in1,
                in2,
                oak::ReadHandle { handle: 9_999_999 }
            ]))?
        );

        expect_eq!(OakStatus::OK, oak::channel_close(out1.handle));
        expect_eq!(OakStatus::OK, oak::channel_close(out2.handle));

        // Still a pending message on in2 even though the only write half for
        // the channel is closed.
        expect_eq!(
            vec![ChannelReadStatus::READ_READY],
            status_convert(oak::wait_on_channels(&[in2]))?
        );

        expect_eq!(OakStatus::OK, oak::channel_close(in1.handle));
        expect_eq!(OakStatus::OK, oak::channel_close(in2.handle));
        Ok(())
    }

    fn test_random_get_raw(&self) -> std::io::Result<()> {
        unsafe {
            expect_eq!(
                OakStatus::ERR_INVALID_ARGS.value() as u32,
                oak::wasm::random_get(invalid_raw_offset() as *mut u8, 1)
            );
        }
        Ok(())
    }

    fn test_random_get(&self) -> std::io::Result<()> {
        let original = vec![0x01, 0x02, 0x03, 0x04];
        let mut data = original.clone();
        expect_eq!(OakStatus::OK, oak::random_get(&mut data));
        // 1 in 2^32 chance of getting back original value
        expect!(data != original);
        Ok(())
    }

    fn test_random_rng(&self) -> std::io::Result<()> {
        let mut rng = oak::rand::OakRng {};
        let x1 = rng.gen::<u64>();
        let x2 = rng.gen::<u64>();
        expect!(x1 != x2);
        Ok(())
    }

    fn test_channel_handle_reuse(&self) -> std::io::Result<()> {
        // Set up a fresh channel with a pending message so wait_on_channels
        // doesn't block.
        let (out_handle, in_handle) = oak::channel_create().unwrap();
        let data = vec![0x01, 0x02, 0x03];
        expect_eq!(OakStatus::OK, oak::channel_write(out_handle, &data, &[]));

        // Read from an invalid handle.
        let mut buffer = Vec::<u8>::with_capacity(5);
        let mut handles = Vec::with_capacity(5);
        expect_eq!(
            OakStatus::ERR_BAD_HANDLE,
            oak::channel_read(
                oak::ReadHandle { handle: 9_987_123 },
                &mut buffer,
                &mut handles
            )
        );
        // Wait on an invalid handle.
        expect_eq!(
            Ok(vec![
                ChannelReadStatus::READ_READY,
                ChannelReadStatus::INVALID_CHANNEL
            ]),
            oak::wait_on_channels(&[in_handle, oak::ReadHandle { handle: 9_987_321 }])
        );

        // Close both of the previously mentioned invalid handles.
        expect_eq!(OakStatus::ERR_BAD_HANDLE, oak::channel_close(9_987_123));
        expect_eq!(OakStatus::ERR_BAD_HANDLE, oak::channel_close(9_987_321));

        expect_eq!(OakStatus::OK, oak::channel_close(out_handle.handle));
        expect_eq!(OakStatus::OK, oak::channel_close(in_handle.handle));
        Ok(())
    }

    fn test_backend_roundtrip(&self) -> std::io::Result<()> {
        // Make a collection of new channels for the backend nodes to read from,
        // and send the read handles to each backend node.
        const COUNT: usize = 3;
        let mut read_handles = Vec::with_capacity(COUNT);
        let mut write_handles = Vec::with_capacity(COUNT);
        for _i in 0..COUNT {
            let (new_write, new_read) = oak::channel_create().unwrap();
            write_handles.push(new_write);
            read_handles.push(new_read.handle);
        }
        for j in 0..BACKEND_COUNT {
            expect_eq!(
                OakStatus::OK,
                oak::channel_write(self.backend_out[j], &[], &read_handles)
            );
        }
        for new_read in read_handles.iter() {
            oak::channel_close(*new_read);
        }

        // Ask the backend node to transmute something by writing a serialized
        // request to one of the new channels that the backends just received
        // the read handles for.
        for new_write in write_handles.iter() {
            let internal_req = InternalMessage {
                msg: "aaa".to_string(),
            };
            let serialized_req = serde_json::to_string(&internal_req)?;

            info!(
                "send serialized message to new channel {}: {}",
                new_write.handle, serialized_req
            );
            let mut new_channel = oak::io::Channel::new(*new_write);
            new_channel.write_all(&serialized_req.into_bytes())?;
            oak::channel_close(new_write.handle);

            // Block until there is a response from one of the backends
            // available.
            let readies = oak::wait_on_channels(&self.backend_in).map_err(|status| {
                std::io::Error::new(
                    std::io::ErrorKind::Other,
                    format!("Wait failure {:?}", status),
                )
            })?;

            // Expect exactly one of the backends to have received
            // the message.
            let mut buffer = Vec::<u8>::with_capacity(256);
            let mut new_in_channel = oak::ReadHandle { handle: 0 };
            for (j, ready) in readies.iter().enumerate() {
                if *ready == ChannelReadStatus::READ_READY {
                    info!("got response from backend[{}]", j);
                    expect_eq!(0, new_in_channel.handle);
                    let mut handles = Vec::with_capacity(1);
                    expect_eq!(
                        OakStatus::OK,
                        oak::channel_read(self.backend_in[j], &mut buffer, &mut handles)
                    );
                    new_in_channel.handle = handles[0];
                }
            }

            // Expect the response to hold a channel read handle.
            // Read the actual transmuted message from this new channel.
            expect_eq!(
                OakStatus::OK,
                oak::channel_read(new_in_channel, &mut buffer, &mut vec![])
            );
            let serialized_rsp = String::from_utf8(buffer).unwrap();
            let internal_rsp: InternalMessage = serde_json::from_str(&serialized_rsp)?;
            expect_eq!("aaaxxx", internal_rsp.msg);

            // Drop the new read channel now we have got the response.
            expect_eq!(OakStatus::OK, oak::channel_close(new_in_channel.handle));
        }
        Ok(())
    }
}
