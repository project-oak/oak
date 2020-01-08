// Copyright 2019 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

//! An implementation of a server for a fidl interface.

use {
    crate::{epitaph, AsyncChannel},
    fuchsia_zircon_status as zx_status,
    futures::task::{AtomicWaker, Context},
    std::sync::atomic::{self, AtomicBool},
};

/// A type used from the innards of server implementations
#[derive(Debug)]
pub struct ServeInner {
    waker: AtomicWaker,
    shutdown: AtomicBool,
    channel: AsyncChannel,
}

impl ServeInner {
    /// Create a new set of server innards.
    pub fn new(channel: AsyncChannel) -> Self {
        let waker = AtomicWaker::new();
        let shutdown = AtomicBool::new(false);
        ServeInner { waker, shutdown, channel }
    }

    /// Get a reference to the inner channel.
    pub fn channel(&self) -> &AsyncChannel {
        &self.channel
    }

    /// Set the server to shutdown.
    pub fn shutdown(&self) {
        self.shutdown.store(true, atomic::Ordering::Relaxed);
        self.waker.wake();
    }

    /// Set the server to shutdown with an epitaph.
    pub fn shutdown_with_epitaph(&self, status: zx_status::Status) {
        let already_shutting_down = self.shutdown.swap(true, atomic::Ordering::Relaxed);
        if !already_shutting_down {
            // Ignore the error, best effort sending an epitaph.
            let _ = epitaph::write_epitaph_impl(&self.channel, status);
            self.waker.wake();
        }
    }

    /// Check if the server has been set to shutdown.
    pub fn poll_shutdown(&self, cx: &mut Context<'_>) -> bool {
        if self.shutdown.load(atomic::Ordering::Relaxed) {
            return true;
        }
        self.waker.register(cx.waker());
        self.shutdown.load(atomic::Ordering::Relaxed)
    }
}
