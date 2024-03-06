//! Split a single value implementing `AsyncRead + AsyncWrite` into separate
//! `AsyncRead` and `AsyncWrite` handles.
//!
//! To restore this read/write object from its `split::ReadHalf` and
//! `split::WriteHalf` use `unsplit`.

use tokio::io::{AsyncRead, AsyncWrite, ReadBuf};

use crate::VsockStream;
use futures::ready;
use std::fmt;
use std::io;
use std::pin::Pin;
use std::sync::Arc;
use std::task::{Context, Poll};

/// Splits a ``VsockStream`` into a readable half and a writeable half
pub fn split(stream: &mut VsockStream) -> (ReadHalf<'_>, WriteHalf<'_>) {
    // Safety: we have an exclusive reference to the stream so we can safely get a readonly and
    // write only reference to it.
    (ReadHalf(stream), WriteHalf(stream))
}

/// The readable half of a value returned from [`split`](split()).
pub struct ReadHalf<'a>(&'a VsockStream);

/// The writable half of a value returned from [`split`](split()).
pub struct WriteHalf<'a>(&'a VsockStream);

impl AsyncRead for ReadHalf<'_> {
    fn poll_read(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &mut ReadBuf<'_>,
    ) -> Poll<io::Result<()>> {
        self.0.poll_read_priv(cx, buf)
    }
}

impl AsyncWrite for WriteHalf<'_> {
    fn poll_write(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &[u8],
    ) -> Poll<Result<usize, io::Error>> {
        self.0.poll_write_priv(cx, buf)
    }

    #[inline]
    fn poll_flush(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Result<(), io::Error>> {
        // Not buffered so flush is a No-op
        Poll::Ready(Ok(()))
    }

    fn poll_shutdown(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Result<(), io::Error>> {
        // TODO: This could maybe block?
        self.0.shutdown(std::net::Shutdown::Write)?;
        Poll::Ready(Ok(()))
    }
}

pub fn split_owned(stream: VsockStream) -> (OwnedReadHalf, OwnedWriteHalf) {
    let inner = Arc::new(Inner::new(stream));

    let rd = OwnedReadHalf {
        inner: inner.clone(),
    };

    let wr = OwnedWriteHalf { inner };

    (rd, wr)
}

/// The readable half of a value returned from [`split_owned`](split_owned()).
pub struct OwnedReadHalf {
    inner: Arc<Inner>,
}

/// The writable half of a value returned from [`split_owned`](split_owned()).
pub struct OwnedWriteHalf {
    inner: Arc<Inner>,
}

struct Inner(tokio::sync::Mutex<VsockStream>);

impl Inner {
    fn new(stream: VsockStream) -> Self {
        Self(tokio::sync::Mutex::new(stream))
    }
}

struct Guard<'a>(tokio::sync::MutexGuard<'a, VsockStream>);

impl OwnedReadHalf {
    /// Checks if this `ReadHalf` and some `WriteHalf` were split from the same
    /// stream.
    pub fn is_pair_of(&self, other: &OwnedWriteHalf) -> bool {
        other.is_pair_of(self)
    }

    /// Reunites with a previously split `WriteHalf`.
    ///
    /// # Panics
    ///
    /// If this `ReadHalf` and the given `WriteHalf` do not originate from the
    /// same `split` operation this method will panic.
    /// This can be checked ahead of time by comparing the stream ID
    /// of the two halves.
    #[track_caller]
    pub fn unsplit(self, wr: OwnedWriteHalf) -> VsockStream {
        if self.is_pair_of(&wr) {
            drop(wr);

            let inner = Arc::try_unwrap(self.inner)
                .ok()
                .expect("`Arc::try_unwrap` failed");

            inner.0.into_inner()
        } else {
            panic!("Unrelated `split::Write` passed to `split::Read::unsplit`.")
        }
    }
}

impl OwnedWriteHalf {
    /// Checks if this `WriteHalf` and some `ReadHalf` were split from the same
    /// stream.
    pub fn is_pair_of(&self, other: &OwnedReadHalf) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    }
}

impl AsyncRead for OwnedReadHalf {
    fn poll_read(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &mut ReadBuf<'_>,
    ) -> Poll<io::Result<()>> {
        let mut inner = ready!(self.inner.poll_lock(cx));
        inner.stream_pin().poll_read(cx, buf)
    }
}

impl AsyncWrite for OwnedWriteHalf {
    fn poll_write(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &[u8],
    ) -> Poll<Result<usize, io::Error>> {
        let mut inner = ready!(self.inner.poll_lock(cx));
        inner.stream_pin().poll_write(cx, buf)
    }

    fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<(), io::Error>> {
        let mut inner = ready!(self.inner.poll_lock(cx));
        inner.stream_pin().poll_flush(cx)
    }

    fn poll_shutdown(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<(), io::Error>> {
        let mut inner = ready!(self.inner.poll_lock(cx));
        inner.stream_pin().poll_shutdown(cx)
    }
}

impl Inner {
    fn poll_lock(&self, cx: &mut Context<'_>) -> Poll<Guard<'_>> {
        if let Ok(guard) = self.0.try_lock() {
            Poll::Ready(Guard(guard))
        } else {
            // Spin... but investigate a better strategy

            std::thread::yield_now();
            cx.waker().wake_by_ref();

            Poll::Pending
        }
    }
}

impl Guard<'_> {
    fn stream_pin(&mut self) -> Pin<&mut VsockStream> {
        // safety: the stream is pinned in `Arc` and the `Guard` ensures mutual
        // exclusion.
        unsafe { Pin::new_unchecked(&mut *self.0) }
    }
}

impl fmt::Debug for OwnedReadHalf {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_struct("split::OwnedReadHalf").finish()
    }
}

impl fmt::Debug for OwnedWriteHalf {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_struct("split::OwnedWriteHalf").finish()
    }
}

impl fmt::Debug for ReadHalf<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("split::ReadHalf").finish()
    }
}

impl fmt::Debug for WriteHalf<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("split::WriteHalf").finish()
    }
}
