/*
 * Copyright 2019 fsyncd, Berlin, Germany.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#![cfg_attr(docsrs, feature(doc_cfg))]

mod listener;
mod split;
mod stream;
#[cfg(feature = "tonic-conn")]
mod tonic_support;

pub use listener::{Incoming, VsockListener};
pub use split::{OwnedReadHalf, OwnedWriteHalf, ReadHalf, WriteHalf};
pub use stream::VsockStream;
#[cfg(feature = "tonic-conn")]
#[cfg_attr(docsrs, doc(cfg(feature = "tonic-conn")))]
pub use tonic_support::VsockConnectInfo;
pub use vsock::{
    VsockAddr, VMADDR_CID_ANY, VMADDR_CID_HOST, VMADDR_CID_HYPERVISOR, VMADDR_CID_LOCAL,
};
