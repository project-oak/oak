// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

//! Epitaph support for Channel and AsyncChannel.

use {
    crate::{
        encoding::{self, EpitaphBody, TransactionHeader, TransactionMessage},
        error::Error,
        AsyncChannel, Channel, Handle,
    },
    fuchsia_zircon_status as zx_status,
};

/// Extension trait that provides Channel-like objects with the ability to send a FIDL epitaph.
pub trait ChannelEpitaphExt {
    /// Consumes the channel and writes an epitaph.
    fn close_with_epitaph(self, status: zx_status::Status) -> Result<(), Error>;
}

impl ChannelEpitaphExt for Channel {
    fn close_with_epitaph(self, status: zx_status::Status) -> Result<(), Error> {
        write_epitaph_impl(&self, status)
    }
}

impl ChannelEpitaphExt for AsyncChannel {
    fn close_with_epitaph(self, status: zx_status::Status) -> Result<(), Error> {
        write_epitaph_impl(&self, status)
    }
}

pub(crate) trait ChannelLike {
    fn write(&self, bytes: &[u8], handles: &mut Vec<Handle>) -> Result<(), zx_status::Status>;
}

impl ChannelLike for Channel {
    fn write(&self, bytes: &[u8], handles: &mut Vec<Handle>) -> Result<(), zx_status::Status> {
        self.write(bytes, handles)
    }
}

impl ChannelLike for AsyncChannel {
    fn write(&self, bytes: &[u8], handles: &mut Vec<Handle>) -> Result<(), zx_status::Status> {
        self.write(bytes, handles)
    }
}

pub(crate) fn write_epitaph_impl<T: ChannelLike>(
    channel: &T,
    status: zx_status::Status,
) -> Result<(), Error> {
    let mut msg = TransactionMessage {
        header: TransactionHeader::new(0, encoding::EPITAPH_ORDINAL),
        body: &mut EpitaphBody { error: status },
    };
    encoding::with_tls_encoded(&mut msg, |bytes, handles| {
        channel.write(&*bytes, &mut *handles).map_err(Error::ServerEpitaphWrite)
    })
}
