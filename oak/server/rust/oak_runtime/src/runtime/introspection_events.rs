//
// Copyright 2020 The Project Oak Authors
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

use crate::{
    proto::oak::introspection_events::{event::EventDetails, Event},
    runtime::{NodeId, Runtime},
};
use log::info;
use prost_types::Timestamp;
use std::time::{SystemTime, UNIX_EPOCH};

pub fn node_id_to_primitive(node_id: NodeId) -> u64 {
    let NodeId(node_id_as_primitive) = node_id;
    node_id_as_primitive
}

fn current_timestamp() -> Timestamp {
    let duration_since_unix_epoch = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("Time went backwards");

    Timestamp {
        seconds: duration_since_unix_epoch.as_secs() as i64,
        nanos: duration_since_unix_epoch.subsec_nanos() as i32,
    }
}

// Introspection event related methods for the Runtime.
impl Runtime {
    /// Generates an introspection event recording a modification to the Runtime's
    /// internal data structures
    #[cfg(feature = "oak_debug")]
    pub fn introspection_event(&self, event_details: EventDetails) {
        let event = Event {
            timestamp: Some(current_timestamp()),
            event_details: Some(event_details),
        };

        // TODO(#913): Push the event over to a channel, to be consumed by the
        // introspection aux server.
        info!("Introspection event recorded: {:?}", event);
    }

    /// no-op implementation, introspection events are a debugging feature.
    #[cfg(not(feature = "oak_debug"))]
    pub fn introspection_event(&self, event_details: EventDetails) {}
}
