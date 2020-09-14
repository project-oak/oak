# RFC#01391: Oak Async SDK

## Objective

Provide first class support for async Rust in the Oak SDK.

## Background

Rust has stable support for
[asynchronous code](https://rust-lang.github.io/async-book) using the `async`
`await` syntax. The Oak SDK does not currently offer native support for
executing futures within nodes or performing asynchronous reads for a channel
using these abstractions.

While the Rust core language provides syntax for writing asynchronous code, and
the standard library provides core traits such as
[`Future`](https://doc.rust-lang.org/std/future/trait.Future.html), these
futures do nothing unless they are `poll`ed by an executor.

Several popular executors exist within the wider Rust ecosystem, such as
[`tokio`](https://github.com/tokio-rs/tokio) and
[`async-std`](https://docs.rs/async-std/1.6.3/async_std/index.html). These are
primarily focused on providing an asynchronous API for I/O in the standard
library, with abstractions for file system access, sockets etc. The Oak SDK does
not provide such functionalities to nodes, and the ABI exposes only a single
blocking call:
[`wait_on_channels`](https://project-oak.github.io/oak/oak_abi/doc/oak_abi/index.html).

While this makes existing executors unsuitable for use in nodes, the small API
surface suggests implementing a custom executor for the Oak SDK is tractable.

## Overview

Support for asynchronous Rust consists of the following components:

- executor for futures that runs in an Oak node.
- async
  [event loop](https://project-oak.github.io/oak/sdk/doc/oak/fn.run_event_loop.html).
- asynchronous primitives for reading from channels. These are tightly coupled
  to the executor.
- spawn functionality for concurrent execution of futures.

Put together, these components allow developers to implement asynchronous nodes.
The
[`hello_world`](https://github.com/project-oak/oak/blob/main/examples/hello_world/module/rust/src/lib.rs)
example node would look similar to:

```rust
oak::entrypoint!(oak_main => |_| {
    // Grpc server setup ...

    oak::run_event_loop(grpc_channel, handler);
});

async fn handler(requests: GrpcInvocations<HelloWorld>) {
    // Initial setup
    let translator = { /* ... */ };

    requests.try_for_each_concurrent(
        /* concurrency limit */ 2,
        |request| async move {
            match request {
                HelloWorld::SayHello(request, response) => {
                    let translation = translator.translate_async(TranslateRequest {
                        text: request.greeting,
                        from: "en".to_string(),
                        to: "fr".to_string(),
                    }).await?;
                    response.send(HelloResponse {
                        reply: format!("BONJOUR {}!", translated_greeting),
                    })?;
                }
                // ...
            }
    }).await.expect("Error handling request");
}
```

Proper client-side streaming
([an open issue](https://github.com/project-oak/oak/issues/97)) becomes
straightforward now that the incoming requests can be represented as a
[`Stream`](https://docs.rs/futures/0.3.5/futures/stream/trait.Stream.html):

```rust
match request {
    // ...
    HelloWorld::BidiHello(requests, responses) => {
        requests.for_each(|request| {
            responses.send(HelloResponse {
                reply: format!("HELLO {}!", request.greeting),
            })?;
        }).await;
    }
}
```

New functions defined on the existing
[`Receiver`](https://project-oak.github.io/oak/sdk/doc/oak/io/struct.Receiver.html)
allow asynchronous reads from channels:

```rust
impl<T: Decodable> Receiver<T> {
    pub fn receive_async(&self) -> ChannelRead<T> { /* ... */ }
    pub fn receive_stream(&self) -> ChannelReadStream<T> { /* ... */ }
}
```

`ChannelRead` mentioned above is the asynchronous channel read primitive,
implementing `Future<Output = Result<T, OakError>`. When `poll`ed, it notifies
the executor that it is waiting for a particular channel to return data. The
executor is in charge of checking for data on the channel, and waking up the
future when the data is ready.

Since waiting on a channel is the only possible blocking operation (writes do
not block in an Oak node), no other primitives are necessary. The
`ChannelReadStream` for example is merely a repeated `ChannelRead` implementing
`Stream<Item = Result<T, OakError>`.

An `oak::spawn` method is provided that works exactly like
[`tokio::spawn`](https://docs.rs/tokio/0.2.22/tokio/fn.spawn.html). When passed
a future, a `JoinHandle` is returned that can be used to await the result of the
spawned future. If this handle is dropped, the executor keeps polling the future
to completion regardless, but there is no way to obtain the result of the
computation.

## Detailed Design

### Handling invocations

Instead of a service trait, an enum is generated from the service definition
that covers all possible invocations:

```rust
enum HelloWorld {
    // Basic request - response
    SayHello(HelloRequest, OneshotWriter<HelloResponse>),
    // request - streaming response
    LotsOfReplies(HelloRequest, MultiWriter<HelloResponse>),
    // streaming request - single response
    LotsOfGreetings(
        RequestStream<HelloRequest>,
        OneshotWriter<HelloResponse>,
    ),
    // streaming request - streaming response
    BidiHello(
        RequestStream<HelloRequest>,
        MultiWriter<HelloResponse>,
    ),
}
```

Each variant is a tuple of (request, response), where the request is either the
plain request or a stream of requests, and the `response` is an object that
allows writing response data.

The type of `run_event_loop` shows how the SDK provides a mapping from a gRPC
channel to the generated type:

```rust
pub fn run_event_loop<T, F, R>(receiver: Receiver<Invocation>, handler: F)
where
    T: TryFrom<oak::grpc::Invocation, OakError>,
    F: FnOnce(GrpcStream<T>) -> R,
    R: Future<Output = ()> + 'static,
```

The `TryFrom` implementation is automatically generated by the service
generator.

`MultiWriter` can be used to send 0 or more messages:

```rust
impl<T: Message> MultiWriter {
    // Note: self by reference
    pub fn send(&self, msg: &T) -> Result<(), OakError> { /* ... */ }

    // Note: optional, automatically called on `Drop`
    pub fn close(self, result: Result<(), oak::grpc::Status>) -> Result<(), OakError>;
}

fn use_multi(w: MultiWriter<HelloResponse>) {
    w.send(HelloResponse::default()).unwrap();
    w.send(HelloResponse::default()).unwrap();
    // Automatically close channel on `Drop`
}
```

The `OneshotWriter` is similar, but only allows a single response to be written:

```rust
impl<T: Message> OneshotWriter {
    // Note: self by value
    pub fn send(self, msg: &T) -> Result<(), OakError> { /* ... */ }

    // Note: optional, automatically called on `Drop`
    pub fn close(self, result: Result<(), oak::grpc::Status>) -> Result<(), OakError>;
}

fn use_oneshot(w: OneshotWriter<HelloResponse>) {
    w.send(HelloResponse::default()).unwrap();
    // `w` can no longer be used.
    // channel is automatically closed.
}
```

### Executor and primitive internals

When a `ChannelRead` is polled and no data is readily available, it must request
the executor to wake it once data does become available. We take a similar
approach to other executors like
[`tokio`](https://github.com/tokio-rs/tokio/blob/master/tokio/src/runtime/context.rs#L7)
here, and make the executor available to `ChannelRead` via thread-local storage
(TLS). Note that for WebAssembly this is equivalent to a global variable, since
threads are not standardized or widely supported. While the initial version of
the executor will be single-threaded, the API is designed to allow for
multithreaded execution.

The executor maintains a set of
[`Waker`](https://doc.rust-lang.org/std/task/struct.Waker.html) objects and the
channels associated with them, which the `ChannelRead` futures add themselves to
when polled. The executor runs the following loop:

```rust
loop {
    // futures_pool: Set of the main event loop future and all `spawn`ed futures.
    // channels: Set of all channels that have wakers associated with them. Populated by `ChannelRead`.
    // wakers: Set of all wakers. Populated by `ChannelRead`.

    // Returns when no future can make progress
    futures_pool.run_until_stalled();

    if futures_pool.is_empty() {
        break;
    }

    let channel_read_statuses = wait_on_channels(&channels);

    // For each ready channel, awake one of the futures that was waiting on it.
    wake_if_ready(channel_read_statuses, wakers);
}
```

Implementing an executor for scratch is hard, unsafe and error-prone, even for a
[very simple basic example](https://github.com/spacejam/extreme#bugs-encountered-over-time).
Instead, we can use an existing and tested
[futures pool](https://docs.rs/futures/0.3.5/futures/executor/struct.LocalPool.html)
that is part of the rust-lang supported `futures` crate, and implement our
executor on top of that. This greatly reduces engineering effort, unsafe code
and testing surface.

## Planning

The initial implementation work for the Async SDK will be done in a separate
`oak_async` crate is under `experimental/`. Most of the changes are
self-contained and can easily live in a separate crate. An extension trait
`ReceiverAsyncExt` can add the required methods to `oak::io::Receiver`. The
`hello_world` and `chat` examples will be used to demonstrate and test the new
functionality.

Rust's futures are a zero-cost abstraction, and even in an `async` function it
is possible to block and call `wait_on_channels` manually (though not
recommended if asynchronous execution is the goal). This means we can make
`async` the default, while still allowing users to call blocking APIs if they
insist on doing so. Convenient methods for blocking such as
[`Receiver::receive`](https://project-oak.github.io/oak/sdk/doc/oak/io/trait.ReceiverExt.html#tymethod.receive)
will be removed from the SDK to prevent users from accidentally blocking.

## Future work

### Timeouts

The Oak SDK does not currently offer a way to suspend execution of a node for a
given amount of time, nor does it allow a timeout value to be specified when
reading from a channel. In the context of asynchronous execution, This means
that either `ChannelRead` should have built-in support for a timeout value, or
functionality should be available to wrap an existing future with a timeout
(like
[`tokio::time::timeout`](https://docs.rs/tokio/0.2.22/tokio/time/fn.timeout.html)).
Two implementation options are described below.

#### Pseudo-node Timer service

One way to implement this would be to create a new pseudo-node that provides a
timer service. No changes to the executor would be required, as a timeout future
would be represented by a `ChannelRead` that resolves when the timer expires.
This approach maps will to the idea of a function to wrap an existing future
with a timeout: the wrapper future would select on both the read and the timeout
future.

- **Pro**: Modular design
- **Pro**: Relatively simple
- **Con**: Inefficient
- **Con**: Requires more code

#### `wait_on_channels` timeout parameter

Another approach would be to add a timeout value to the `wait_on_channels` ABI
call. When a `ChannelRead` registers to be woken up by the executor, it also
provides a timeout value. The executor then needs to maintain this timeout,
making sure to set the timeout value in the `wait_on_channels` call to the
lowest of all pending reads with a timeout. `wait_on_channels` should also
report the amount of timed that was spent waiting to the caller, as the executor
will need to adjust the timeout values of all reads that do not have data ready
at this point.

- **Pro**: Efficient
- **Con**: Relatively complex
- **Con**: Monolithic design
