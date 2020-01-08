// Copyright 2018 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

//! An implementation of a client for a fidl interface.

use {
    crate::{
        encoding::{
            decode_transaction_header, Decodable, Decoder, Encodable, Encoder, EpitaphBody,
            TransactionHeader, TransactionMessage,
        },
        handle::{AsyncChannel, Handle, MessageBuf},
        Error,
    },
    fuchsia_zircon_status as zx_status,
    futures::{
        future::{self, AndThen, Either, Future, FutureExt, Ready, TryFutureExt},
        ready,
        stream::{FusedStream, Stream},
        task::{Context, Poll, Waker},
    },
    parking_lot::Mutex,
    slab::Slab,
    std::{collections::VecDeque, marker::Unpin, mem, ops::Deref, pin::Pin, sync::Arc},
};

#[cfg(target_os = "fuchsia")]
use fuchsia_zircon::AsHandleRef;

fn decode_transaction_body<D: Decodable>(mut buf: MessageBuf) -> Result<D, Error> {
    let (bytes, handles) = buf.split_mut();
    let (header, body_bytes) = decode_transaction_header(bytes)?;
    let mut output = D::new_empty();
    Decoder::decode_into(&header, body_bytes, handles, &mut output)?;
    Ok(output)
}

fn decode_transaction_body_fut<D: Decodable>(buf: MessageBuf) -> Ready<Result<D, Error>> {
    future::ready(decode_transaction_body(buf))
}

/// A FIDL client which can be used to send buffers and receive responses via a channel.
#[derive(Debug, Clone)]
pub struct Client {
    inner: Arc<ClientInner>,
}

/// A future representing the raw response to a FIDL query.
pub type RawQueryResponseFut = Either<Ready<Result<MessageBuf, Error>>, MessageResponse>;

/// A future representing the decoded response to a FIDL query.
pub type QueryResponseFut<D> = AndThen<
    RawQueryResponseFut,
    Ready<Result<D, Error>>,
    fn(MessageBuf) -> Ready<Result<D, Error>>,
>;

/// A FIDL transaction id. Will not be zero for a message that includes a response.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Txid(u32);
/// A message interest id.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct InterestId(usize);

impl InterestId {
    fn from_txid(txid: Txid) -> Self {
        InterestId(txid.0 as usize - 1)
    }

    fn as_raw_id(&self) -> usize {
        self.0
    }
}

impl Txid {
    fn from_interest_id(int_id: InterestId) -> Self {
        Txid((int_id.0 + 1) as u32)
    }

    /// Get the raw u32 transaction ID.
    pub fn as_raw_id(&self) -> u32 {
        self.0
    }
}

impl From<u32> for Txid {
    fn from(txid: u32) -> Self {
        Self(txid)
    }
}

impl Client {
    /// Create a new client.
    ///
    /// `channel` is the asynchronous channel over which data is sent and received.
    /// `event_ordinals` are the ordinals on which events will be received.
    pub fn new(channel: AsyncChannel) -> Client {
        Client {
            inner: Arc::new(ClientInner {
                channel: channel,
                message_interests: Mutex::new(Slab::<MessageInterest>::new()),
                event_channel: Mutex::default(),
                epitaph: Mutex::default(),
            }),
        }
    }

    /// Attempt to convert the `Client` back into a channel.
    ///
    /// This will only succeed if there are no active clones of this `Client`
    /// and no currently-alive `EventReceiver` or `MessageResponse`s that
    /// came from this `Client`.
    pub fn into_channel(self) -> Result<AsyncChannel, Self> {
        match Arc::try_unwrap(self.inner) {
            Ok(ClientInner { channel, .. }) => Ok(channel),
            Err(inner) => Err(Self { inner }),
        }
    }

    /// Retrieve the stream of event messages for the `Client`.
    /// Panics if the stream was already taken.
    pub fn take_event_receiver(&self) -> EventReceiver {
        {
            let mut lock = self.inner.event_channel.lock();

            if let EventListener::None = lock.listener {
                lock.listener = EventListener::WillPoll;
            } else {
                panic!("Event stream was already taken");
            }
        }

        EventReceiver { inner: self.inner.clone(), terminated: false }
    }

    /// Send an encodable message without expecting a response.
    pub fn send<T: Encodable>(&self, body: &mut T, ordinal: u64) -> Result<(), Error> {
        let msg = &mut TransactionMessage { header: TransactionHeader::new(0, ordinal), body };
        crate::encoding::with_tls_encoded(msg, |bytes, handles| {
            self.send_raw_msg(&**bytes, handles)
        })
    }

    /// Send an encodable query and receive a decodable response.
    pub fn send_query<E: Encodable, D: Decodable>(
        &self,
        msg: &mut E,
        ordinal: u64,
    ) -> QueryResponseFut<D> {
        let res_fut = self.send_raw_query(|tx_id, bytes, handles| {
            let msg = &mut TransactionMessage {
                header: TransactionHeader::new(tx_id.as_raw_id(), ordinal),
                body: msg,
            };
            Encoder::encode(bytes, handles, msg)?;
            Ok(())
        });

        res_fut.and_then(decode_transaction_body_fut::<D>)
    }

    /// Send a raw message without expecting a response.
    pub fn send_raw_msg(&self, buf: &[u8], handles: &mut Vec<Handle>) -> Result<(), Error> {
        Ok(self.inner.channel.write(buf, handles).map_err(|e| Error::ClientWrite(e.into()))?)
    }

    /// Send a raw query and receive a response future.
    pub fn send_raw_query<F>(&self, msg_from_id: F) -> RawQueryResponseFut
    where
        F: for<'a, 'b> FnOnce(Txid, &'a mut Vec<u8>, &'b mut Vec<Handle>) -> Result<(), Error>,
    {
        let id = self.inner.register_msg_interest();
        let res = crate::encoding::with_tls_coding_bufs(|bytes, handles| {
            msg_from_id(Txid::from_interest_id(id), bytes, handles)?;
            self.inner.channel.write(bytes, handles).map_err(|e| Error::ClientWrite(e.into()))?;
            Ok::<(), Error>(())
        });

        match res {
            Ok(()) => {
                MessageResponse { id: Txid::from_interest_id(id), client: Some(self.inner.clone()) }
                    .right_future()
            }
            Err(e) => futures::future::ready(Err(e)).left_future(),
        }
    }
}

#[must_use]
/// A future which polls for the response to a client message.
#[derive(Debug)]
pub struct MessageResponse {
    id: Txid,
    // `None` if the message response has been recieved
    client: Option<Arc<ClientInner>>,
}

impl Unpin for MessageResponse {}

impl Future for MessageResponse {
    type Output = Result<MessageBuf, Error>;
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = &mut *self;
        let res;
        {
            let client = this.client.as_ref().ok_or(Error::PollAfterCompletion)?;
            res = client.poll_recv_msg_response(this.id, cx);
        }

        // Drop the client reference if the response has been received
        if let Poll::Ready(Ok(_)) = res {
            let client = this.client.take().expect("MessageResponse polled after completion");
            client.wake_any();
        }

        res
    }
}

impl Drop for MessageResponse {
    fn drop(&mut self) {
        if let Some(client) = &self.client {
            client.deregister_msg_interest(InterestId::from_txid(self.id));
            client.wake_any();
        }
    }
}

/// An enum reprenting either a resolved message interest or a task on which to alert
/// that a response message has arrived.
#[derive(Debug)]
enum MessageInterest {
    /// A new `MessageInterest`
    WillPoll,
    /// A task is waiting to receive a response, and can be awoken with `Waker`.
    Waiting(Waker),
    /// A message has been received, and a task will poll to receive it.
    Received(MessageBuf),
    /// A message has not been received, but the person interested in the response
    /// no longer cares about it, so the message should be discared upon arrival.
    Discard,
}

impl MessageInterest {
    /// Check if a message has been received.
    fn is_received(&self) -> bool {
        if let MessageInterest::Received(_) = *self {
            true
        } else {
            false
        }
    }

    fn unwrap_received(self) -> MessageBuf {
        if let MessageInterest::Received(buf) = self {
            buf
        } else {
            panic!("EXPECTED received message")
        }
    }
}

/// A stream of events as `MessageBuf`s.
#[derive(Debug)]
pub struct EventReceiver {
    inner: Arc<ClientInner>,
    terminated: bool,
}

impl Unpin for EventReceiver {}

impl FusedStream for EventReceiver {
    fn is_terminated(&self) -> bool {
        self.terminated
    }
}

/// This implementation holds up two invariants
///   (1) After `None` is returned, the next poll panics
///   (2) Until this instance is dropped, no other EventReceiver may claim the
///       event channel by calling Client::take_event_receiver.
impl Stream for EventReceiver {
    type Item = Result<MessageBuf, Error>;

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        if self.is_terminated() {
            panic!("polled EventReceiver after `None`");
        }
        Poll::Ready(match ready!(self.inner.as_ref().poll_recv_event(cx)) {
            Ok(x) => Some(Ok(x)),
            Err(Error::ClientChannelClosed(_)) => {
                // The channel is closed, set our internal state so that on the
                // next poll_next() we panic and is_terminated() returns an
                // appropriate value.
                self.terminated = true;
                None
            }
            Err(e) => Some(Err(e)),
        })
    }
}

impl Drop for EventReceiver {
    fn drop(&mut self) {
        self.inner.event_channel.lock().listener = EventListener::None;
        self.inner.wake_any();
    }
}

#[derive(Debug, Default)]
struct EventChannel {
    listener: EventListener,
    queue: VecDeque<MessageBuf>,
}

#[derive(Debug)]
enum EventListener {
    /// No one is listening for the event
    None,
    /// Someone is listening for the event but has not yet polled
    WillPoll,
    /// Someone is listening for the event and can be woken via the `Waker`
    Some(Waker),
}

impl Default for EventListener {
    fn default() -> Self {
        EventListener::None
    }
}

/// A shared client channel which tracks EXPECTED and received responses
#[derive(Debug)]
struct ClientInner {
    channel: AsyncChannel,

    /// A map of message interests to either `None` (no message received yet)
    /// or `Some(DecodeBuf)` when a message has been received.
    /// An interest is registered with `register_msg_interest` and deregistered
    /// by either receiving a message via a call to `poll_recv` or manually
    /// deregistering with `deregister_msg_interest`
    message_interests: Mutex<Slab<MessageInterest>>,

    /// A queue of received events and a waker for the task to receive them.
    event_channel: Mutex<EventChannel>,

    /// The server provided epitaph, or None if the channel is not closed.
    epitaph: Mutex<Option<zx_status::Status>>,
}

impl Deref for Client {
    type Target = AsyncChannel;

    fn deref(&self) -> &Self::Target {
        &self.inner.channel
    }
}

impl ClientInner {
    /// Registers interest in a response message.
    ///
    /// This function returns a `usize` ID which should be used to send a message
    /// via the channel. Responses are then received using `poll_recv`.
    fn register_msg_interest(&self) -> InterestId {
        // TODO(cramertj) use `try_from` here and assert that the conversion from
        // `usize` to `u32` hasn't overflowed.
        InterestId(self.message_interests.lock().insert(MessageInterest::WillPoll))
    }

    fn poll_recv_event(&self, cx: &mut Context<'_>) -> Poll<Result<MessageBuf, Error>> {
        {
            // Update the EventListener with the latest waker, remove any stale WillPoll state
            let mut lock = self.event_channel.lock();
            lock.listener = EventListener::Some(cx.waker().clone());
        }

        let epitaph = self.recv_all()?;

        let mut lock = self.event_channel.lock();

        if let Some(msg_buf) = lock.queue.pop_front() {
            Poll::Ready(Ok(msg_buf))
        } else {
            if let Some(status) = epitaph {
                Poll::Ready(Err(Error::ClientChannelClosed(status)))
            } else {
                Poll::Pending
            }
        }
    }

    fn poll_recv_msg_response(
        &self,
        txid: Txid,
        cx: &mut Context<'_>,
    ) -> Poll<Result<MessageBuf, Error>> {
        let interest_id = InterestId::from_txid(txid);
        {
            // If have not yet received anything, update any stale WillPoll or Waiting(stale waker)
            // message interest for the current message.
            let mut message_interests = self.message_interests.lock();
            let message_interest = message_interests
                .get_mut(interest_id.as_raw_id())
                .expect("Polled unregistered interest");
            if !message_interest.is_received() {
                *message_interest = MessageInterest::Waiting(cx.waker().clone());
            }
        }

        let epitaph = self.recv_all()?;

        let mut message_interests = self.message_interests.lock();
        if message_interests
            .get(interest_id.as_raw_id())
            .expect("Polled unregistered interest")
            .is_received()
        {
            // If, by happy accident, we just raced to getting the result,
            // then yay! Return success.
            let buf = message_interests.remove(interest_id.as_raw_id()).unwrap_received();
            Poll::Ready(Ok(buf))
        } else {
            if let Some(status) = epitaph {
                Poll::Ready(Err(Error::ClientChannelClosed(status)))
            } else {
                Poll::Pending
            }
        }
    }

    /// Poll for the receipt of any response message or an event.
    ///
    /// Returns whether or not the channel is closed.
    fn recv_all(&self) -> Result<Option<zx_status::Status>, Error> {
        // TODO(cramertj) return errors if one has occured _ever_ in recv_all, not just if
        // one happens on this call.
        loop {
            // Acquire a mutex so that only one thread can read from the underlying channel
            // at a time. Channel is already synchronized, but we need to also decode the
            // FIDL message header atomically so that epitaphs can be properly handled.
            let mut epitaph_lock = self.epitaph.lock();
            if epitaph_lock.is_some() {
                return Ok(*epitaph_lock);
            }
            let buf = {
                let waker = match self.get_pending_waker() {
                    Some(v) => v,
                    None => return Ok(None),
                };
                let cx = &mut Context::from_waker(&waker);

                let mut buf = MessageBuf::new();
                let result = self.channel.recv_from(cx, &mut buf);
                match result {
                    Poll::Ready(Ok(())) => {}
                    Poll::Ready(Err(zx_status::Status::PEER_CLOSED)) => {
                        // The channel has been closed, and no epitaph was received. Set the epitaph to PEER_CLOSED.
                        *epitaph_lock = Some(zx_status::Status::PEER_CLOSED);
                        // The task that calls this method also has its Waker woken. This could be
                        // optimized by excluding this task, but since this occurs on channel close,
                        // it is not a critical optimization.
                        self.wake_all();
                        return Ok(*epitaph_lock);
                    }
                    Poll::Ready(Err(e)) => return Err(Error::ClientRead(e)),
                    Poll::Pending => {
                        return Ok(None);
                    }
                };
                buf
            };

            let (header, body_bytes) =
                decode_transaction_header(buf.bytes()).map_err(|_| Error::InvalidHeader)?;
            if !header.is_compatible() {
                return Err(Error::IncompatibleMagicNumber(header.magic_number()));
            }
            if header.is_epitaph() {
                // Received an epitaph. Record this so that future operations receive the same
                // epitaph.
                let handles = &mut [];
                let mut epitaph_body = EpitaphBody::new_empty();
                Decoder::decode_into(&header, &body_bytes, handles, &mut epitaph_body)?;
                *epitaph_lock = Some(epitaph_body.error);
                // The task that calls this method also has its Waker woken. This could be
                // optimized by excluding this task, but since this occurs on channel close,
                // it is not a critical optimization.
                self.wake_all();
                return Ok(*epitaph_lock);
            }

            // Epitaph handling is done, so the lock is no longer required.
            drop(epitaph_lock);

            if header.tx_id() == 0 {
                // received an event
                let mut lock = self.event_channel.lock();
                lock.queue.push_back(buf);
                if let EventListener::Some(_) = lock.listener {
                    if let EventListener::Some(waker) =
                        mem::replace(&mut lock.listener, EventListener::WillPoll)
                    {
                        waker.wake();
                    }
                }
            } else {
                // received a message response
                let recvd_interest_id = InterestId::from_txid(Txid(header.tx_id()));

                // Look for a message interest with the given ID.
                // If one is found, store the message so that it can be picked up later.
                let mut message_interests = self.message_interests.lock();
                let raw_recvd_interest_id = recvd_interest_id.as_raw_id();
                if let Some(&MessageInterest::Discard) =
                    message_interests.get(raw_recvd_interest_id)
                {
                    message_interests.remove(raw_recvd_interest_id);
                } else if let Some(entry) = message_interests.get_mut(raw_recvd_interest_id) {
                    let old_entry = mem::replace(entry, MessageInterest::Received(buf));
                    if let MessageInterest::Waiting(waker) = old_entry {
                        // Wake up the task to let them know a message has arrived.
                        waker.wake();
                    }
                }
            }
        }
    }

    fn deregister_msg_interest(&self, InterestId(id): InterestId) {
        let mut lock = self.message_interests.lock();
        if lock[id].is_received() {
            lock.remove(id);
        } else {
            lock[id] = MessageInterest::Discard;
        }
    }

    /// Gets an arbitrary task that has polled on this channel and has not yet
    /// gotten a response.
    fn get_pending_waker(&self) -> Option<Waker> {
        {
            let lock = self.message_interests.lock();
            for (_, message_interest) in lock.iter() {
                if let MessageInterest::Waiting(waker) = message_interest {
                    return Some(waker.clone());
                }
            }
        }
        {
            let lock = self.event_channel.lock();
            if let EventListener::Some(waker) = &lock.listener {
                return Some(waker.clone());
            }
        }
        None
    }

    /// Wakes up an arbitrary task that has begun polling on the channel so that
    /// it will call recv_all.
    fn wake_any(&self) {
        if let Some(waker) = self.get_pending_waker() {
            waker.wake();
        }
    }

    /// Wakes all tasks that have polled on this channel.
    fn wake_all(&self) {
        {
            let mut lock = self.message_interests.lock();
            for (_, message_interest) in lock.iter_mut() {
                // Only wake and replace the tasks that have polled and have Wakers.
                // Otherwise a task has received a response would have that buffer
                // overridden.
                if let MessageInterest::Waiting(_) = message_interest {
                    if let MessageInterest::Waiting(waker) =
                        mem::replace(message_interest, MessageInterest::WillPoll)
                    {
                        waker.wake();
                    }
                }
            }
        }
        {
            let lock = self.event_channel.lock();
            if let EventListener::Some(waker) = &lock.listener {
                waker.wake_by_ref();
            }
        }
    }
}

#[cfg(target_os = "fuchsia")]
pub mod sync {
    //! Synchronous FIDL Client

    use fuchsia_zircon as zx;

    use super::*;

    /// A synchronous client for making FIDL calls.
    #[derive(Debug)]
    pub struct Client {
        // Underlying channel
        channel: zx::Channel,

        // Reusable buffer for r/w
        buf: zx::MessageBuf,
    }

    // TODO: remove this and allow multiple overlapping queries on the same channel.
    pub(super) const QUERY_TX_ID: u32 = 42;

    impl Client {
        /// Create a new synchronous FIDL client.
        pub fn new(channel: zx::Channel) -> Self {
            Client { channel, buf: zx::MessageBuf::new() }
        }

        /// Get the underlying channel out of the client.
        pub fn into_channel(self) -> zx::Channel {
            self.channel
        }

        /// Send a new message.
        pub fn send<E: Encodable>(&mut self, msg: &mut E, ordinal: u64) -> Result<(), Error> {
            self.buf.clear();
            let (buf, handles) = self.buf.split_mut();
            let msg =
                &mut TransactionMessage { header: TransactionHeader::new(0, ordinal), body: msg };
            Encoder::encode(buf, handles, msg)?;
            self.channel.write(buf, handles).map_err(|e| Error::ClientWrite(e.into()))?;
            Ok(())
        }

        /// Send a new message expecting a response.
        pub fn send_query<E: Encodable, D: Decodable>(
            &mut self,
            msg: &mut E,
            ordinal: u64,
            deadline: zx::Time,
        ) -> Result<D, Error> {
            // Write the message into the channel
            self.buf.clear();
            let (buf, handles) = self.buf.split_mut();
            let msg = &mut TransactionMessage {
                header: TransactionHeader::new(QUERY_TX_ID, ordinal),
                body: msg,
            };
            Encoder::encode(buf, handles, msg)?;
            self.channel.write(buf, handles).map_err(|e| Error::ClientWrite(e.into()))?;

            // Read the response
            self.buf.clear();
            match self.channel.read(&mut self.buf) {
                Ok(()) => {}
                Err(zx_status::Status::SHOULD_WAIT) => {
                    let signals = self
                        .channel
                        .wait_handle(
                            zx::Signals::CHANNEL_READABLE | zx::Signals::CHANNEL_PEER_CLOSED,
                            deadline,
                        )
                        .map_err(|e| Error::ClientRead(e.into()))?;
                    if !signals.contains(zx::Signals::CHANNEL_READABLE) {
                        debug_assert!(signals.contains(zx::Signals::CHANNEL_PEER_CLOSED));
                        return Err(Error::ClientRead(zx_status::Status::PEER_CLOSED));
                    }
                    self.channel.read(&mut self.buf).map_err(|e| Error::ClientRead(e.into()))?;
                }
                Err(e) => return Err(Error::ClientRead(e.into())),
            }
            let (buf, handles) = self.buf.split_mut();
            let (header, body_bytes) = decode_transaction_header(buf)?;
            // TODO(fxb/7848): Check received ordinal against sent ordinal. For
            // the migration, we disable this check and rely only on the tx_id
            // since the ordinal sent may not be the ordinal received.
            if header.tx_id() != QUERY_TX_ID {
                return Err(Error::UnexpectedSyncResponse);
            }
            let mut output = D::new_empty();
            Decoder::decode_into(&header, body_bytes, handles, &mut output)?;
            Ok(output)
        }
    }
}

#[cfg(all(test, target_os = "fuchsia"))]
mod tests {
    use super::*;
    use {
        crate::encoding::MAGIC_NUMBER_INITIAL,
        crate::epitaph::{self, ChannelEpitaphExt},
        anyhow::{Context as _, Error},
        fuchsia_async as fasync,
        fuchsia_async::{DurationExt, TimeoutExt},
        fuchsia_zircon as zx,
        fuchsia_zircon::DurationNum,
        futures::{join, FutureExt, StreamExt},
        futures_test::task::new_count_waker,
        std::thread,
        test_util::assert_matches,
    };

    const SEND_ORDINAL_HIGH_BYTE: u8 = 42;
    const SEND_ORDINAL: u64 = 42 << 32;
    const SEND_DATA: u8 = 55;

    #[rustfmt::skip]
    fn expected_sent_bytes(tx_id_low_byte: u8) -> [u8; 24] {
        [
            tx_id_low_byte, 0, 0, 0, // 32 bit tx_id
            1, 0, 0, // flags (unions encoded as xunions)
            MAGIC_NUMBER_INITIAL,
            0, 0, 0, 0, // low bytes of 64 bit ordinal
            SEND_ORDINAL_HIGH_BYTE, 0, 0, 0, // high bytes of 64 bit ordinal
            SEND_DATA, // 8 bit data
            0, 0, 0, 0, 0, 0, 0, // 7 bytes of padding after our 1 byte of data
        ]
    }

    fn send_transaction(header: TransactionHeader, channel: &zx::Channel) {
        let (bytes, handles) = (&mut vec![], &mut vec![]);
        encode_transaction(header, bytes, handles);
        channel.write(bytes, handles).expect("Server channel write failed");
    }

    fn encode_transaction(
        header: TransactionHeader,
        bytes: &mut Vec<u8>,
        handles: &mut Vec<zx::Handle>,
    ) {
        let event = &mut TransactionMessage { header: header, body: &mut SEND_DATA };
        Encoder::encode(bytes, handles, event).expect("Encoding failure");
    }

    #[test]
    fn sync_client() -> Result<(), Error> {
        let (client_end, server_end) = zx::Channel::create().context("chan create")?;
        let mut client = sync::Client::new(client_end);
        client.send(&mut SEND_DATA, SEND_ORDINAL).context("sending")?;
        let mut received = MessageBuf::new();
        server_end.read(&mut received).context("reading")?;
        let one_way_tx_id = 0;
        assert_eq!(received.bytes(), expected_sent_bytes(one_way_tx_id));
        Ok(())
    }

    #[test]
    fn sync_client_with_response() -> Result<(), Error> {
        let (client_end, server_end) = zx::Channel::create().context("chan create")?;
        let mut client = sync::Client::new(client_end);
        thread::spawn(move || {
            // Server
            let mut received = MessageBuf::new();
            server_end
                .wait_handle(zx::Signals::CHANNEL_READABLE, zx::Time::after(5.seconds()))
                .expect("failed to wait for channel readable");
            server_end.read(&mut received).expect("failed to read on server end");
            let (buf, _handles) = received.split_mut();
            let (header, _body_bytes) = decode_transaction_header(buf).expect("server decode");
            assert_eq!(header.tx_id(), sync::QUERY_TX_ID);
            assert_eq!(header.ordinal(), SEND_ORDINAL);
            send_transaction(TransactionHeader::new(header.tx_id(), header.ordinal()), &server_end);
        });
        let response_data = client
            .send_query::<u8, u8>(&mut SEND_DATA, SEND_ORDINAL, zx::Time::after(5.seconds()))
            .context("sending query")?;
        assert_eq!(SEND_DATA, response_data);
        Ok(())
    }

    #[fasync::run_singlethreaded(test)]
    async fn client() {
        let (client_end, server_end) = zx::Channel::create().unwrap();
        let client_end = AsyncChannel::from_channel(client_end).unwrap();
        let client = Client::new(client_end);

        let server = AsyncChannel::from_channel(server_end).unwrap();
        let receiver = async move {
            let mut buffer = MessageBuf::new();
            server.recv_msg(&mut buffer).await.expect("failed to recv msg");
            let one_way_tx_id = 0;
            assert_eq!(buffer.bytes(), expected_sent_bytes(one_way_tx_id));
        };

        // add a timeout to receiver so if test is broken it doesn't take forever
        let receiver = receiver
            .on_timeout(300.millis().after_now(), || panic!("did not receive message in time!"));

        let sender = fasync::Timer::new(100.millis().after_now()).map(|()| {
            client.send(&mut SEND_DATA, SEND_ORDINAL).expect("failed to send msg");
        });

        join!(receiver, sender);
    }

    #[fasync::run_singlethreaded(test)]
    async fn client_with_response() {
        let (client_end, server_end) = zx::Channel::create().unwrap();
        let client_end = AsyncChannel::from_channel(client_end).unwrap();
        let client = Client::new(client_end);

        let server = AsyncChannel::from_channel(server_end).unwrap();
        let mut buffer = MessageBuf::new();
        let receiver = async move {
            server.recv_msg(&mut buffer).await.expect("failed to recv msg");
            let two_way_tx_id = 1u8;
            assert_eq!(buffer.bytes(), expected_sent_bytes(two_way_tx_id));

            let (bytes, handles) = (&mut vec![], &mut vec![]);
            let header = TransactionHeader::new(two_way_tx_id as u32, 42);
            encode_transaction(header, bytes, handles);
            server.write(bytes, handles).expect("Server channel write failed");
        };

        // add a timeout to receiver so if test is broken it doesn't take forever
        let receiver = receiver
            .on_timeout(300.millis().after_now(), || panic!("did not receiver message in time!"));

        let sender = client
            .send_query::<u8, u8>(&mut SEND_DATA, SEND_ORDINAL)
            .map_ok(|x| assert_eq!(x, SEND_DATA))
            .unwrap_or_else(|e| panic!("fidl error: {:?}", e));

        // add a timeout to receiver so if test is broken it doesn't take forever
        let sender = sender
            .on_timeout(300.millis().after_now(), || panic!("did not receive response in time!"));

        let ((), ()) = join!(receiver, sender);
    }

    #[fasync::run_singlethreaded(test)]
    async fn client_with_response_receives_epitaph() {
        let (client_end, server_end) = zx::Channel::create().unwrap();
        let client_end = fasync::Channel::from_channel(client_end).unwrap();
        let client = Client::new(client_end);

        let server = fasync::Channel::from_channel(server_end).unwrap();
        let mut buffer = zx::MessageBuf::new();
        let receiver = async move {
            server.recv_msg(&mut buffer).await.expect("failed to recv msg");
            server
                .close_with_epitaph(zx_status::Status::UNAVAILABLE)
                .expect("failed to write epitaph");
        };
        // add a timeout to receiver so if test is broken it doesn't take forever
        let receiver = receiver
            .on_timeout(300.millis().after_now(), || panic!("did not receive message in time!"));

        let sender = async move {
            let result = client.send_query::<u8, u8>(&mut 55, 42 << 32).await;
            assert_matches!(
                result,
                Err(crate::Error::ClientChannelClosed(zx_status::Status::UNAVAILABLE))
            );
        };
        // add a timeout to sender so if test is broken it doesn't take forever
        let sender = sender
            .on_timeout(300.millis().after_now(), || panic!("did not receive response in time!"));

        let ((), ()) = join!(receiver, sender);
    }

    #[fasync::run_singlethreaded(test)]
    #[should_panic]
    async fn event_cant_be_taken_twice() {
        let (client_end, _) = zx::Channel::create().unwrap();
        let client_end = AsyncChannel::from_channel(client_end).unwrap();
        let client = Client::new(client_end);
        let _foo = client.take_event_receiver();
        client.take_event_receiver();
    }

    #[fasync::run_singlethreaded(test)]
    async fn event_can_be_taken_after_drop() {
        let (client_end, _) = zx::Channel::create().unwrap();
        let client_end = AsyncChannel::from_channel(client_end).unwrap();
        let client = Client::new(client_end);
        let foo = client.take_event_receiver();
        drop(foo);
        client.take_event_receiver();
    }

    #[fasync::run_singlethreaded(test)]
    async fn receiver_termination_test() {
        let (client_end, _) = zx::Channel::create().unwrap();
        let client_end = AsyncChannel::from_channel(client_end).unwrap();
        let client = Client::new(client_end);
        let mut foo = client.take_event_receiver();
        assert!(!foo.is_terminated(), "receiver should not report terminated before being polled");
        let _ = foo.next().await;
        assert!(
            foo.is_terminated(),
            "receiver should report terminated after seeing channel is closed"
        );
    }

    #[fasync::run_singlethreaded(test)]
    #[should_panic(expected = "polled EventReceiver after `None`")]
    async fn receiver_cant_be_polled_more_than_once_on_closed_stream() {
        let (client_end, _) = zx::Channel::create().unwrap();
        let client_end = AsyncChannel::from_channel(client_end).unwrap();
        let client = Client::new(client_end);
        let foo = client.take_event_receiver();
        drop(foo);
        let mut bar = client.take_event_receiver();
        assert!(bar.next().await.is_none(), "read on closed channel should return none");
        // this should panic
        let _ = bar.next().await;
    }

    #[fasync::run_singlethreaded(test)]
    async fn event_can_be_taken() {
        let (client_end, _) = zx::Channel::create().unwrap();
        let client_end = AsyncChannel::from_channel(client_end).unwrap();
        let client = Client::new(client_end);
        client.take_event_receiver();
    }

    #[fasync::run_singlethreaded(test)]
    async fn event_received() {
        let (client_end, server_end) = zx::Channel::create().unwrap();
        let client_end = AsyncChannel::from_channel(client_end).unwrap();
        let client = Client::new(client_end);

        // Send the event from the server
        let server = AsyncChannel::from_channel(server_end).unwrap();
        let (bytes, handles) = (&mut vec![], &mut vec![]);
        let header = TransactionHeader::new(0, 5);
        encode_transaction(header, bytes, handles);
        server.write(bytes, handles).expect("Server channel write failed");
        drop(server);

        let recv = client
            .take_event_receiver()
            .into_future()
            .then(|(x, stream)| {
                let x = x.expect("should contain one element");
                let x = x.expect("fidl error");
                let x: i32 = decode_transaction_body(x).expect("failed to decode event");
                assert_eq!(x, 55);
                stream.into_future()
            })
            .map(|(x, _stream)| assert!(x.is_none(), "should have emptied"));

        // add a timeout to receiver so if test is broken it doesn't take forever
        let recv =
            recv.on_timeout(300.millis().after_now(), || panic!("did not receive event in time!"));

        recv.await;
    }

    /// Tests that the event receiver can be taken, the stream read to the end,
    /// the receiver dropped, and then a new receiver gotten from taking the
    /// stream again.
    #[fasync::run_singlethreaded(test)]
    async fn receiver_can_be_taken_after_end_of_stream() {
        let (client_end, server_end) = zx::Channel::create().unwrap();
        let client_end = AsyncChannel::from_channel(client_end).unwrap();
        let client = Client::new(client_end);

        // Send the event from the server
        let server = AsyncChannel::from_channel(server_end).unwrap();
        let (bytes, handles) = (&mut vec![], &mut vec![]);
        let header = TransactionHeader::new(0, 5);
        encode_transaction(header, bytes, handles);
        server.write(bytes, handles).expect("Server channel write failed");
        drop(server);

        // Create a block to make sure the first event receiver is dropped.
        // Creating the block is a bit of paranoia, because awaiting the
        // future moves the receiver anyway.
        {
            let recv = client
                .take_event_receiver()
                .into_future()
                .then(|(x, stream)| {
                    let x = x.expect("should contain one element");
                    let x = x.expect("fidl error");
                    let x: i32 = decode_transaction_body(x).expect("failed to decode event");
                    assert_eq!(x, 55);
                    stream.into_future()
                })
                .map(|(x, _stream)| assert!(x.is_none(), "should have emptied"));

            // add a timeout to receiver so if test is broken it doesn't take forever
            let recv = recv
                .on_timeout(300.millis().after_now(), || panic!("did not receive event in time!"));

            recv.await;
        }

        // if we take the event stream again, we should be able to get the next
        // without a panic, but that should be none
        let mut c = client.take_event_receiver();
        assert!(
            c.next().await.is_none(),
            "receiver on closed channel should return none on first call"
        );
    }

    #[fasync::run_singlethreaded(test)]
    async fn event_incompatible_format() {
        let (client_end, server_end) = zx::Channel::create().unwrap();
        let client_end = fasync::Channel::from_channel(client_end).unwrap();
        let client = Client::new(client_end);

        // Send the event from the server
        let server = fasync::Channel::from_channel(server_end).unwrap();
        let (bytes, handles) = (&mut vec![], &mut vec![]);
        let header = TransactionHeader::new_full(0, 5, &crate::encoding::Context {}, 0);
        encode_transaction(header, bytes, handles);
        server.write(bytes, handles).expect("Server channel write failed");
        drop(server);

        let mut event_receiver = client.take_event_receiver();
        let recv = event_receiver.next().map(|event| {
            assert_matches!(event, Some(Err(crate::Error::IncompatibleMagicNumber(0))))
        });

        // add a timeout to receiver so if test is broken it doesn't take forever
        let recv =
            recv.on_timeout(300.millis().after_now(), || panic!("did not receive event in time!"));

        recv.await;
    }

    #[fasync::run_singlethreaded(test)]
    async fn polling_event_receives_epitaph() {
        let (client_end, server_end) = zx::Channel::create().unwrap();
        let client_end = fasync::Channel::from_channel(client_end).unwrap();
        let client = Client::new(client_end);

        // Send the epitaph from the server
        let server = fasync::Channel::from_channel(server_end).unwrap();
        server.close_with_epitaph(zx_status::Status::UNAVAILABLE).expect("failed to write epitaph");

        let mut event_receiver = client.take_event_receiver();
        let recv = event_receiver.next().map(|x| assert!(x.is_none(), "should be None"));

        // add a timeout to receiver so if test is broken it doesn't take forever
        let recv =
            recv.on_timeout(300.millis().after_now(), || panic!("did not receive event in time!"));

        recv.await;
    }

    #[test]
    fn client_always_wakes_pending_futures() {
        let mut executor = fasync::Executor::new().unwrap();

        let (client_end, server_end) = zx::Channel::create().unwrap();
        let client_end = AsyncChannel::from_channel(client_end).unwrap();
        let client = Client::new(client_end);

        let mut event_receiver = client.take_event_receiver();

        // first poll on a response
        let (response_waker, response_waker_count) = new_count_waker();
        let response_cx = &mut Context::from_waker(&response_waker);
        let mut response_txid = Txid(0);
        let mut response_future = client.send_raw_query(|tx_id, bytes, handles| {
            response_txid = tx_id;
            let header = TransactionHeader::new(response_txid.as_raw_id(), 42);
            encode_transaction(header, bytes, handles);
            Ok(())
        });
        assert!(response_future.poll_unpin(response_cx).is_pending());

        // then, poll on an event
        let (event_waker, event_waker_count) = new_count_waker();
        let event_cx = &mut Context::from_waker(&event_waker);
        assert!(event_receiver.poll_next_unpin(event_cx).is_pending());

        // at this point, nothing should have been woken
        assert_eq!(response_waker_count.get(), 0);
        assert_eq!(event_waker_count.get(), 0);

        // next, simulate an event coming in
        send_transaction(TransactionHeader::new(0, 5), &server_end);

        // get event loop to deliver readiness notifications to channels
        let _ = executor.run_until_stalled(&mut future::pending::<()>());

        // either response_waker or event_waker should be woken
        assert_eq!(response_waker_count.get() + event_waker_count.get(), 1);
        let last_response_waker_count = response_waker_count.get();

        // we'll pretend event_waker was woken, and have that poll out the event
        assert!(event_receiver.poll_next_unpin(event_cx).is_ready());

        // next, simulate a response coming in
        send_transaction(TransactionHeader::new(response_txid.as_raw_id(), 42), &server_end);

        // get event loop to deliver readiness notifications to channels
        let _ = executor.run_until_stalled(&mut future::pending::<()>());

        // response waker should have been woken again
        assert_eq!(response_waker_count.get(), last_response_waker_count + 1);
    }

    #[test]
    fn client_always_wakes_pending_futures_on_epitaph() {
        let mut executor = fasync::Executor::new().unwrap();

        let (client_end, server_end) = zx::Channel::create().unwrap();
        let client_end = fasync::Channel::from_channel(client_end).unwrap();
        let client = Client::new(client_end);

        let mut event_receiver = client.take_event_receiver();

        // first poll on a response
        let (response1_waker, response1_waker_count) = new_count_waker();
        let response1_cx = &mut Context::from_waker(&response1_waker);
        let mut response1_future = client.send_raw_query(|tx_id, bytes, handles| {
            let header = TransactionHeader::new(tx_id.as_raw_id(), 42);
            encode_transaction(header, bytes, handles);
            Ok(())
        });
        assert!(response1_future.poll_unpin(response1_cx).is_pending());

        // then, poll on an event
        let (event_waker, event_waker_count) = new_count_waker();
        let event_cx = &mut Context::from_waker(&event_waker);
        assert!(event_receiver.poll_next_unpin(event_cx).is_pending());

        // poll on another response
        let (response2_waker, response2_waker_count) = new_count_waker();
        let response2_cx = &mut Context::from_waker(&response2_waker);
        let mut response2_future = client.send_raw_query(|tx_id, bytes, handles| {
            let header = TransactionHeader::new(tx_id.as_raw_id(), 42);
            encode_transaction(header, bytes, handles);
            Ok(())
        });
        assert!(response2_future.poll_unpin(response2_cx).is_pending());

        let wakers = vec![response1_waker_count, response2_waker_count, event_waker_count];

        // get event loop to deliver readiness notifications to channels
        let _ = executor.run_until_stalled(&mut future::pending::<()>());

        // at this point, nothing should have been woken
        assert_eq!(0, wakers.iter().fold(0, |acc, x| acc + x.get()));

        // next, simulate an epitaph without closing
        epitaph::write_epitaph_impl(&server_end, zx_status::Status::UNAVAILABLE)
            .expect("wrote epitaph");

        // get event loop to deliver readiness notifications to channels
        let _ = executor.run_until_stalled(&mut future::pending::<()>());

        // one waker should have woken up, since reading from a channel only supports
        // a single waker.
        assert_eq!(1, wakers.iter().fold(0, |acc, x| acc + x.get()));

        // pretend that response1 woke and poll that to completion.
        assert_matches!(
            response1_future.poll_unpin(response1_cx),
            Poll::Ready(Err(crate::Error::ClientChannelClosed(zx_status::Status::UNAVAILABLE)))
        );

        // get event loop to deliver readiness notifications to channels
        let _ = executor.run_until_stalled(&mut future::pending::<()>());

        // response1 will have woken all other tasks again.
        // NOTE: The task that is waking all other tasks is also woken.
        assert_eq!(1 + wakers.len(), wakers.iter().fold(0, |acc, x| acc + x.get()));

        // poll response2 to completion.
        assert_matches!(
            response2_future.poll_unpin(response2_cx),
            Poll::Ready(Err(crate::Error::ClientChannelClosed(zx_status::Status::UNAVAILABLE)))
        );

        // poll the event stream to completion.
        assert!(event_receiver.poll_next_unpin(event_cx).is_ready());
    }

    #[fasync::run_singlethreaded(test)]
    async fn client_allows_take_event_stream_even_if_event_delivered() {
        let (client_end, server_end) = zx::Channel::create().unwrap();
        let client_end = AsyncChannel::from_channel(client_end).unwrap();
        let client = Client::new(client_end);

        // first simulate an event coming in, even though nothing has polled
        send_transaction(TransactionHeader::new(0, 5), &server_end);

        // next, poll on a response
        let (response_waker, _response_waker_count) = new_count_waker();
        let response_cx = &mut Context::from_waker(&response_waker);
        let mut response_future = client.send_query::<u8, u8>(&mut 55, 42);
        assert!(response_future.poll_unpin(response_cx).is_pending());

        // then, make sure we can still take the event receiver without panicking
        let mut _event_receiver = client.take_event_receiver();
    }
}
