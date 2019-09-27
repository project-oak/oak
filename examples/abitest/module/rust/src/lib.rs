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

#[macro_use]
extern crate log;
extern crate abitest_common;
#[macro_use]
extern crate expect;
extern crate oak;
extern crate oak_log;
extern crate protobuf;
extern crate regex;
extern crate serde;

mod proto;

use abitest_common::InternalMessage;
use oak::grpc::OakNode;
use oak::{grpc, OakStatus};
use proto::abitest::{ABITestRequest, ABITestResponse, ABITestResponse_TestResult};
use proto::abitest_grpc::{dispatch, OakABITestServiceNode};
use protobuf::ProtobufEnum;
use std::collections::HashMap;
use std::io::Write;

struct FrontendNode {
    grpc_in: oak::ReadHandle,
    grpc_out: oak::WriteHandle,
    backend_out: oak::WriteHandle,
    backend_in: oak::ReadHandle,
}

#[no_mangle]
pub extern "C" fn oak_main() -> i32 {
    match std::panic::catch_unwind(|| {
        let node = FrontendNode::new();
        let grpc_in = node.grpc_in;
        let grpc_out = node.grpc_out;
        oak::grpc::event_loop(node, grpc_in, grpc_out)
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
            grpc_out: oak::WriteHandle {
                handle: oak::channel_find("gRPC_output"),
            },
            backend_out: oak::WriteHandle {
                handle: oak::channel_find("to_backend"),
            },
            backend_in: oak::ReadHandle {
                handle: oak::channel_find("from_backend"),
            },
        }
    }
    fn invoke(&mut self, method: &str, req: &[u8], out: oak::WriteHandle) {
        dispatch(self, method, req, out)
    }
}

impl OakABITestServiceNode for FrontendNode {
    fn run_tests(&mut self, req: ABITestRequest) -> grpc::Result<ABITestResponse> {
        info!("Run tests matching {}", req.filter);
        let filter = regex::Regex::new(&req.filter).unwrap();
        let mut results = protobuf::RepeatedField::<ABITestResponse_TestResult>::new();

        // Manual registry of all tests.
        // TODO(#237): Add some macro wizardry for registering test methods based on an attribute
        type TestFn = fn(&FrontendNode) -> std::io::Result<()>;
        let mut tests: HashMap<&str, TestFn> = HashMap::new();
        tests.insert("ChannelFind", FrontendNode::test_channel_find);
        tests.insert("ChannelCreate", FrontendNode::test_channel_create);
        tests.insert("ChannelClose", FrontendNode::test_channel_close);
        tests.insert("ChannelRead", FrontendNode::test_channel_read);
        tests.insert("ChannelWrite", FrontendNode::test_channel_write);
        tests.insert("WaitOnChannels", FrontendNode::test_channel_wait);
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

impl FrontendNode {
    fn test_channel_find(&self) -> std::io::Result<()> {
        // Idempotent result.
        expect_eq!(self.grpc_in.handle, oak::channel_find("gRPC_input"));
        expect_eq!(self.grpc_out.handle, oak::channel_find("gRPC_output"));
        expect_eq!(self.backend_out.handle, oak::channel_find("to_backend"));
        expect_eq!(self.backend_in.handle, oak::channel_find("from_backend"));
        // Whitespace is significant.
        expect_eq!(0, oak::channel_find(" gRPC_input"));
        expect_eq!(0, oak::channel_find(" gRPC_input "));
        expect_eq!(0, oak::channel_find("bogus"));
        expect_eq!(0, oak::channel_find(""));
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

    fn test_channel_close(&self) -> std::io::Result<()> {
        let (w, r) = oak::channel_create().unwrap();
        expect_eq!(OakStatus::OK, oak::channel_close(w.handle));
        expect_eq!(OakStatus::OK, oak::channel_close(r.handle));
        expect_eq!(OakStatus::ERR_BAD_HANDLE, oak::channel_close(w.handle));
        expect_eq!(OakStatus::ERR_BAD_HANDLE, oak::channel_close(99999));

        // Can close ends in either order.
        let (w, r) = oak::channel_create().unwrap();
        expect_eq!(OakStatus::OK, oak::channel_close(r.handle));
        expect_eq!(OakStatus::OK, oak::channel_close(w.handle));
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
        expect_eq!(OakStatus::OK, oak::channel_write(out_channel, &data, &[]));

        expect_eq!(OakStatus::OK, oak::channel_close(out_channel.handle));
        Ok(())
    }

    fn test_channel_wait(&self) -> std::io::Result<()> {
        // Consume a lot of channel handles before we start, to ensure we're
        // working with handles that don't fit in a single byte.
        self.test_channel_create()?;

        let (out1, in1) = oak::channel_create().unwrap();
        let (out2, in2) = oak::channel_create().unwrap();

        // Set up first channel with a pending message.
        let data = vec![0x01, 0x02, 0x03];
        expect_eq!(OakStatus::OK, oak::channel_write(out1, &data, &[]));

        expect_eq!(
            vec![in1],
            status_convert(oak::wait_on_channels(&[in1, in2]))?
        );
        // No read so still ready (level triggered not edge triggered).
        expect_eq!(
            vec![in1],
            status_convert(oak::wait_on_channels(&[in1, in2]))?
        );

        expect_eq!(OakStatus::OK, oak::channel_write(out2, &data, &[]));
        expect_eq!(
            vec![in1, in2],
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
            vec![in2],
            status_convert(oak::wait_on_channels(&[in1, in2]))?
        );

        // Write channels and nonsense handles are ignored.
        expect_eq!(
            vec![in2],
            status_convert(oak::wait_on_channels(&[
                in1,
                in2,
                oak::ReadHandle {
                    handle: out1.handle
                }
            ]))?
        );
        expect_eq!(
            vec![in2],
            status_convert(oak::wait_on_channels(&[
                in1,
                in2,
                oak::ReadHandle { handle: 9_999_999 }
            ]))?
        );

        expect_eq!(OakStatus::OK, oak::channel_close(out1.handle));
        expect_eq!(OakStatus::OK, oak::channel_close(in1.handle));
        expect_eq!(OakStatus::OK, oak::channel_close(out2.handle));
        expect_eq!(OakStatus::OK, oak::channel_close(in2.handle));
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
            Ok(vec![in_handle]),
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
        // Ask the backend node to transmute something.
        let internal_req = InternalMessage {
            msg: "aaa".to_string(),
        };
        let serialized_req = serde_json::to_string(&internal_req)?;
        info!("send serialized message to backend: {}", serialized_req);
        let mut backend_channel = oak::io::Channel::new(self.backend_out);
        backend_channel.write_all(&serialized_req.into_bytes())?;

        // Block until there is a response from the backend available.
        let read_handles = vec![self.backend_in];
        match oak::wait_on_channels(&read_handles) {
            Ok(_ready_handles) => (),
            Err(status) => {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::Other,
                    format!("Wait failure {:?}", status),
                ));
            }
        }

        let mut buffer = Vec::<u8>::with_capacity(256);
        let mut handles = Vec::with_capacity(1);
        expect_eq!(
            OakStatus::OK,
            oak::channel_read(self.backend_in, &mut buffer, &mut handles)
        );

        // Expect to receive a channel read handle.
        // Read the actual response from the new channel.
        let new_in_channel = oak::ReadHandle { handle: handles[0] };
        expect_eq!(
            OakStatus::OK,
            oak::channel_read(new_in_channel, &mut buffer, &mut vec![])
        );
        let serialized_rsp = String::from_utf8(buffer).unwrap();
        let internal_rsp: InternalMessage = serde_json::from_str(&serialized_rsp)?;
        expect_eq!("aaaxxx", internal_rsp.msg);

        // Drop the new read channel now we have got the response.
        oak::channel_close(handles[0]);
        Ok(())
    }
}
