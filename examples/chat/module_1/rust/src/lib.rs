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

use chat_common::proto::chat::ReceivedMessage;
use log::{info, warn};
use protobuf::ProtobufEnum;

#[no_mangle]
pub extern "C" fn backend_oak_main(handle: u64) -> i32 {
    match std::panic::catch_unwind(|| main(handle)) {
        Ok(rc) => rc,
        Err(_) => oak::OakStatus::ERR_INTERNAL.value(),
    }
}

pub fn main(in_handle: u64) -> i32 {
    oak_log::init_default();
    oak::set_panic_hook();
    info!("per-room node started");

    let in_channel = oak::ReadHandle {
        handle: oak::Handle::from_raw(in_handle),
    };

    let mut rsp_writers: Vec<oak::grpc::ChannelResponseWriter> = Vec::with_capacity(1);
    loop {
        // Wait for something on our single input channel.
        let ready_status = match oak::wait_on_channels(&[in_channel]) {
            Ok(ready_status) => ready_status,
            Err(err) => {
                info!("room terminating with {}", err.value());
                for writer in &mut rsp_writers {
                    writer.close(Ok(())).expect("Failed to close writer");
                }
                return err.value();
            }
        };
        if ready_status[0] != oak::ChannelReadStatus::READ_READY {
            continue;
        }

        // Read a message and possible additional outbound handles.
        let mut buf = Vec::<u8>::with_capacity(512);
        let mut handles = Vec::with_capacity(2);
        let status = oak::channel_read(in_channel, &mut buf, &mut handles);
        if status != oak::OakStatus::OK {
            return status.value();
        }
        for handle in handles {
            info!("add handle {:?} to output writers", handle);
            rsp_writers.push(oak::grpc::ChannelResponseWriter::new(oak::WriteHandle {
                handle,
            }));
        }
        if buf.is_empty() {
            continue;
        }
        let msg: ReceivedMessage = match protobuf::parse_from_bytes(&buf) {
            Err(_) => {
                warn!("failed to parse ReceivedMessage");
                return oak::OakStatus::ERR_INTERNAL.value();
            }
            Ok(m) => m,
        };

        info!(
            "{}: fan out message from {} to {} outputs",
            msg.room_name,
            msg.user_handle,
            rsp_writers.len()
        );
        for writer in &mut rsp_writers {
            writer
                .write(&msg, oak::grpc::WriteMode::KeepOpen)
                .expect("Failed to write message");
        }
    }
}
